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
       val show : t -> string
       val typ : t -> typ_term
       val symbol_of : t -> symbol
       val is_global : t -> bool
     end)
    (T : sig
       type t
       type var = Var.t
       val construct : C.t formula -> (var * C.t term) list -> t
       val guard : t -> C.t formula
       val mem_transform : var -> t -> bool
       val get_transform : var -> t -> C.t term
       val zero : t
       val one : t
       val star : t -> t
       val exists : (Var.t -> bool) -> t -> t
     end)
    (VarMap : BatMap.S with type key = Var.t)
    (W : sig
       val wt : int * int -> T.t
       val length : Pathexpr.nested Pathexpr.t -> int VarMap.t
       val length_to : int -> int VarMap.t
     end)
= struct

  let srk = C.context

  (* Canonical name for the ith version of a variable *)
  let _var_i_symbol =
    Memo.memo (fun (v, i) ->
        if i = 0 then Var.symbol_of v
        else
          mk_symbol srk
            ~name:(Var.show v ^ string_of_int i)
            (Var.typ v :> typ))
  let var_i_symbol v i = _var_i_symbol (v, i)

  let of_tr vars tr =
    let (pre_subst, transform) =
      VarMap.fold (fun v (l, u) (m, trans) ->
          let const i = mk_const srk (var_i_symbol v i) in
          (Symbol.Map.add (Var.symbol_of v) (const l) m,
           if T.mem_transform v tr then (const u, T.get_transform v tr)::trans
           else if l <> u then (const u, const l)::trans
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
    |> rewrite srk ~up:(SrkSimplify.simplify_terms_rewriter srk % Nonlinear.simplify_terms_rewriter srk)
  
  let to_tr vars phi =
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
             let const i = mk_const srk (var_i_symbol v i) in
             (Term.set_expr srk (const l) (const u))::lst
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
    let vars' =
      VarMap.mapi (fun v (l, u) ->
          let d = VarMap.find_default 0 v len in
          if d = 0 then (l, u) else (l+1, l+1+d))
        vars
    in
    f pe vars' |> to_tr vars' |> T.star |> of_tr vars

  and project vars pe =
    let vars' =
      VarMap.merge (fun _ lu d ->
          match lu, d with
          | Some (l, u), _ -> Some (l, u)
          | None, Some d -> Some (0, d)
          | _ -> assert false)
        vars
        (W.length pe)
    in
    f pe vars' |> to_tr vars' |> T.exists Var.is_global
    |> of_tr vars

  and table = Pathexpr.Table.create 991 

  and f pe vars =
    (* Printf.printf "%s(%d-%d) %s\n" (VarMap.choose vars |> fst |> Var.show) (VarMap.choose vars |> snd |> fst) (VarMap.choose vars |> snd |> snd) (Pathexpr.show pe) ; *)
    if Pathexpr.Table.mem table pe then
      let (phi, vars') = Pathexpr.Table.find table pe in
      (* Check if the variables disgree in any place. It's alright if
         some variable appears in one but not the other --- that means
         it's irrelevant to the transition. *)
      let disagreements =
        VarMap.merge (fun _ lu lu' ->
            match lu, lu' with
            | Some (l, u), Some (l', u') ->
               if l = l' && u = u' then None
               else Some ((l, u), (l', u'))
            | _ -> None)
          vars vars'
      in
      if VarMap.is_empty disagreements then phi
      else
        let _ = Log.logf ~level:`warn "Irreducible program flow" in
        (* to_tr vars' phi |> of_tr vars *)
        assert false
    else
      let res =
        match Pathexpr.destruct pe with
        | `Edge e -> of_tr vars (W.wt e) 
        | `Mul (left, right) -> mul vars left right
        | `Add (left, right) -> add vars left right
        | `Star pe' -> star vars pe'
        | `Segment pe' -> project vars pe'
        | `One -> one vars
        | `Zero -> zero
      in
      Pathexpr.Table.add table pe (res, vars) ;
      (* Printf.printf "%s:\n %s\n\n" (Pathexpr.show pe) (Formula.show srk res) ; *)
      res

  let src =
    let algebra = function
      | `Edge (s, _) -> Some s
      | `Star s | `Segment s
        | `Mul (s, _) | `Add (s, _) -> s
      | `One | `Zero -> None
    in
    let table = Pathexpr.mk_table () in
    Pathexpr.eval_nested ~table ~algebra
  
  let transition pe =
    match Pathexpr.destruct pe with
    | `Zero -> T.zero
    | `One -> T.one
    | _ ->
       (* Guess which variables to use (this is always correct on
          reducible flow graphs!) *)
       let pre = match src pe with
         | Some s -> W.length_to s
         | None -> VarMap.empty
       in
       let vars =
         VarMap.merge (fun _ l d ->
                let l = Option.value ~default:0 l in
                let d = Option.value ~default:0 d in
                Some (l, l + d))
           pre (W.length pe)
       in
       f pe vars |> to_tr vars

  let forget pred = Pathexpr.Table.forget table pred

end
