open BatPervasives
open Syntax

include Log.Make(struct let name = "srk.skolemizedTransition" end)

module Make
    (C : sig
       type t
       val context : t context
     end)
    (Var : sig
       type t
       val compare : t -> t -> int
       val show : t -> string
       val typ : t -> typ_term
       val symbol_of : t -> symbol
     end)
    (T : sig
       type t
       type var = Var.t
       val construct : C.t formula -> (var * C.t term) list -> t
       val guard : t -> C.t formula
       val mem_transform : var -> t -> bool
       val get_transform : var -> t -> C.t term
       val domain : (C.t Iteration.exp_op) ref
     end)
    (VarMap : BatMap.S with type key = Var.t)
    (W : sig
       val wt : int * int -> T.t
       val length : Pathexpr.nested Pathexpr.t -> int VarMap.t
       val guess_vars : Pathexpr.nested Pathexpr.t -> (int * int) VarMap.t
    end)
= struct

  let srk = C.context

  module VarSet = BatSet.Make(Var)

  (* todo: use hashconsing! *)
  module HT = BatHashtbl
  let table = HT.create 991
  
  (* Canonical name for the ith version of a variable *)
  let _var_i_symbol =
    Memo.memo (fun (v, i) ->
        if i = 0 then Var.symbol_of v
        else
          mk_symbol srk
            ~name:(Var.show v ^ string_of_int i)
            (Var.typ v :> typ))
  let var_i_symbol v i = _var_i_symbol (v, i)

  let simplify = rewrite srk ~up:(SrkSimplify.simplify_terms_rewriter srk % Nonlinear.simplify_terms_rewriter srk)

  let of_tr tr vars =
    let (pre_subst, transform) =
      VarMap.fold (fun v (l, u) (m, trans) ->
          let symt i = mk_const srk (var_i_symbol v i) in
          (Symbol.Map.add (Var.symbol_of v) (symt l) m
           |> Symbol.Map.add (var_i_symbol v u) (symt u),
           if T.mem_transform v tr then (symt u, T.get_transform v tr)::trans
           else if l <> u then (symt u, symt l)::trans
           else trans))
        vars
        (Symbol.Map.empty, [])
    in
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol srk sym in
          let typ = typ_symbol srk sym in
          mk_const srk (mk_symbol srk ~name typ))
    in
    let freshen s =
      match Symbol.Map.find_opt s pre_subst with
      | Some t -> t
      | None -> fresh_skolem s
    in
    let post_defs =
      List.map (fun (s, t) ->
          Term.set_expr srk s (substitute_const srk freshen t))
        transform
    in
    mk_and srk ((substitute_const srk freshen (T.guard tr))::post_defs)
    |> simplify
  
  let to_tr phi vars =
    let (transform, subst) =
      VarMap.fold (fun v (l, u) (transform, subst) ->
          ((if l = u then transform else (v, (mk_const srk (var_i_symbol v u)))::transform),
           Symbol.Map.add (var_i_symbol v l) (mk_const srk (Var.symbol_of v)) subst))
        vars
        ([], Symbol.Map.empty)
    in
    T.construct (substitute_map srk subst (phi)) transform

  let one vars =
    VarMap.fold (fun v (l, u) lst ->
           if l <> u then
             let sym i = mk_const srk (var_i_symbol v i) in
             (Term.set_expr srk (sym l) (sym u))::lst
           else lst)
      vars []
    |> mk_and srk
      
  let zero = mk_false srk

  let rec mul vars left right =
    let left_vars =
      VarMap.merge (fun _ lu d ->
          match lu, d with
          | Some (l, _), Some d -> Some (l, l+d)
          | _ -> None)
        vars (W.length left)
    in
    let right_vars =
      VarMap.merge (fun _ lu d ->
          match lu, d with
          | Some (l, u), Some d -> Some (l+d, u)
          | Some (l, u), None -> Some (l, u)
          | _ -> None)
        vars (W.length left)
    in
    mk_and srk [f left left_vars ; f right right_vars]
  
  and add vars left right =
    mk_or srk [f left vars ; f right vars]

  and star vars pe =
    let len = W.length pe in
    let (vars', prepost, subst) =
      VarMap.fold (fun v (l, u) (vars', prepost, subst) ->
          let d = VarMap.find_default 0 v len in
          let (l', u') = if d = 0 then (l, u) else (l+1, l+1+d) in
          let sym = var_i_symbol v in
          (VarMap.add v (l', u') vars',
           (sym l', sym u')::prepost,
           Symbol.Map.add (sym l') (mk_const srk (sym l)) subst
           |> Symbol.Map.add (sym u') (mk_const srk (sym u))))
        vars
        (VarMap.empty, [], Symbol.Map.empty)
    in
    let exists s = Symbol.Map.mem s subst in
    let tf = TransitionFormula.make ~exists (simplify (f pe vars')) prepost in
    (* Compute the closure *)
    let closure = Iteration.closure !T.domain (Iteration.Solver.make srk tf) in
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol srk sym in
          let typ = typ_symbol srk sym in
          mk_const srk (mk_symbol srk ~name typ))
    in
    substitute_const srk
      (fun s -> match Symbol.Map.find_opt s subst with
                | Some t -> t
                | None -> fresh_skolem s)
      closure 

  and project vars pe =
    let keep = 
      VarMap.fold (fun v (l, u) keep ->
          let sym = var_i_symbol v in
          Symbol.Set.add (sym l) keep
          |> Symbol.Set.add (sym u))
        vars
        Symbol.Set.empty
    in
    let vars' =
      VarMap.merge (fun _ lu d ->
          match lu, d with
          | Some (l, u), _ -> Some (l, u)
          | None, Some d -> Some (0, d)
          | _ -> assert false)
        vars
        (W.length pe)
    in
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol srk sym in
          let typ = typ_symbol srk sym in
          mk_const srk (mk_symbol srk ~name typ))
    in
    substitute_const srk 
      (fun s -> if Symbol.Set.mem s keep then (mk_const srk s) else fresh_skolem s)
      (f pe vars')

  and f pe vars =
    if HT.mem table pe then
      let (phi, vars') = HT.find table pe in
      if not (VarMap.equal (=) vars vars') then
        let _ = Printf.printf "woops\n" in
        assert false
      else phi
    else
      let res =
        match Pathexpr.destruct pe with
        | `Edge e -> of_tr (W.wt e) vars
        | `Mul (left, right) -> mul vars left right
        | `Add (left, right) -> add vars left right
        | `Star pe' -> star vars pe'
        | `Segment pe' -> project vars pe'
        | `One -> one vars
        | `Zero -> zero
      in
      HT.add table pe (res, vars) ;
      (* Printf.printf "%s(%d-%d) %s : %s\n" (VarMap.choose vars |> fst |> Var.show) (VarMap.choose vars |> snd |> fst) (VarMap.choose vars |> snd |> snd) (Pathexpr.show pe) (Formula.show srk res) ; *)
      res

  let transition pe =
    let vars = W.guess_vars pe in
    let phi = f pe vars in
    to_tr phi vars

end
