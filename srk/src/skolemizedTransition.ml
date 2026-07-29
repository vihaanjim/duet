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
       val compare : t -> t -> int
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
       val domain : (C.t Iteration.exp_op) ref
       val equal : t -> t -> bool
     end)
= struct

  module VarMap = BatMap.Make(Var)

  type t =
    { bounds : (int * int) VarMap.t ;
      formula: C.t formula }

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

  let _of_tr tr bounds =
    let (pre_subst, transform) =
      VarMap.fold (fun v (l, u) (m, trans) ->
          let sym i = mk_const srk (var_i_symbol v i) in
          (Symbol.Map.add (Var.symbol_of v) (sym l) m,
           if T.mem_transform v tr then (sym u, T.get_transform v tr)::trans
           else if l <> u then (sym u, sym l)::trans
           else trans))
        bounds
        (Symbol.Map.empty, [])
    in
    let post_defs =
      List.map (fun (s, t) ->
          Term.set_expr srk s (substitute_map srk pre_subst t))
        transform
    in
    let formula =
      mk_and srk ((substitute_map srk pre_subst (T.guard tr))::post_defs)
      |> rewrite srk ~up:(SrkSimplify.simplify_terms_rewriter srk % Nonlinear.simplify_terms_rewriter srk)
    in
    { bounds ; formula }

  let of_tr tr bounds =
    let bounds = VarMap.of_enum bounds in
    _of_tr tr bounds

  let to_tr st =
    let (transform, subst) =
      VarMap.fold (fun v (l, u) (transform, subst) ->
          ((if l = u then transform else (v, (mk_const srk (var_i_symbol v u)))::transform),
           Symbol.Map.add (var_i_symbol v l) (mk_const srk (Var.symbol_of v)) subst))
        st.bounds
        ([], Symbol.Map.empty)
    in
    T.construct (substitute_map srk subst (st.formula)) transform

  let one = { bounds = VarMap.empty ; formula = mk_true srk }
  let zero = { bounds = VarMap.empty ; formula = mk_false srk }

  let new_bounds f left right =
    let lbounds = ref VarMap.empty in
    let rbounds = ref VarMap.empty in
    let add bounds v b = bounds := VarMap.add v b !bounds in
    let bounds =
      VarMap.union (fun v b1 b2 ->
          let (b, b1', b2') = f b1 b2 in
          if b1 <> b1' then add lbounds v b1' ;
          if b2 <> b2' then add rbounds v b2' ;
          Some b)
        left right
    in
    (bounds, !lbounds, !rbounds)

  let adjust_formula stf bounds =
    if VarMap.is_empty bounds then stf.formula
    else 
      let fresh_skolem =
        Memo.memo (fun sym ->
            let name = show_symbol srk sym in
            let typ = typ_symbol srk sym in
            mk_const srk (mk_symbol srk ~name typ))
      in
      let (keep, change) =
        VarMap.fold (fun v (l, u) (keep, change) ->
            let sym = var_i_symbol v in
            match VarMap.find_opt v bounds with
            | Some (l', u') ->
               (keep,
                Symbol.Map.add (sym l) (mk_const srk (sym l')) change
                |> Symbol.Map.add (sym u) (mk_const srk (sym u')))
            | None -> (Symbol.Set.add (sym l) keep
                       |> Symbol.Set.add (sym u),
                       change))
          stf.bounds
          (Symbol.Set.empty, Symbol.Map.empty)
      in
      substitute_const srk (fun s ->
          if Symbol.Set.mem s keep then mk_const srk s
          else match Symbol.Map.find_opt s change with
               | Some t -> t
               | None -> fresh_skolem s)
        stf.formula

  let mul left right =
    (* Printf.printf "%s AND %s\n" (Formula.show srk left.formula) (Formula.show srk right.formula) ; *)
    let (bounds, lbounds, rbounds) =
      new_bounds (fun (ll, lu) (rl, ru) ->
          if lu <> rl then
            (* Leave the one with a bigger distance unchanged *)
            if ru - rl > lu - ll then
              ((rl - lu + ll, ru), (rl - lu + ll, rl), (rl, ru))
            else ((ll, lu + ru - rl), (ll, lu), (lu, lu + ru - rl))
          else ((ll, ru), (ll, lu), (rl, ru)))
        left.bounds right.bounds
    in
    { bounds ; formula = mk_and srk
                           [adjust_formula left lbounds ;
                            adjust_formula right rbounds]}
  
  let add left right =
    (* Printf.printf "%s OR %s\n" (Formula.show srk left.formula) (Formula.show srk right.formula) ; *)
    let (bounds, lbounds, rbounds) =
      new_bounds (fun (ll, lu) (rl, ru) ->
          if ll <> rl || lu <> ru then
            (* Leave the one with a bigger distance unchanged *)
            if ru - rl > lu - ll then
              ((rl, ru), (rl, ru), (rl, ru))
            else ((ll, lu), (ll, lu), (ll, lu))
          else ((ll, lu), (ll, lu), (ll, lu)))
        left.bounds right.bounds
    in
    { bounds ; formula = mk_or srk
                           [adjust_formula left lbounds ;
                            adjust_formula right rbounds]}

  let star stf =
    (* TODO: consider substituting in fresh variables? *)
    (* Convert to a transition formula and find substitution *)
    let (bounds, prepost, syms, subst) =
      VarMap.fold (fun v (l, u) (bounds, prepost, syms, subst) ->
          let l' = if l = u then l else l-1 and u' = l in
          let sym = var_i_symbol v in
          (VarMap.add v (l', u') bounds,
           (sym l, sym u)::prepost,
           Symbol.Set.add (sym l) syms
           |> Symbol.Set.add (sym u),
           Symbol.Map.add (sym l) (mk_const srk (sym l')) subst
           |> Symbol.Map.add (sym u) (mk_const srk (sym u'))))
        stf.bounds
        (VarMap.empty, [], Symbol.Set.empty, Symbol.Map.empty)
    in
    let body =
      stf.formula
      |> rewrite srk ~up:(SrkSimplify.simplify_terms_rewriter srk % Nonlinear.simplify_terms_rewriter srk)
    in
    let exists s = Symbol.Set.mem s syms in
    let tf = TransitionFormula.make ~exists body prepost in
    (* Compute the closure *)
    let closure = Iteration.closure !T.domain (Iteration.Solver.make srk tf) in
    { bounds ; formula = substitute_map srk subst closure }

  let project stf =
    let bounds =
      VarMap.fold (fun v (l, _) bounds ->
          if Var.is_global v then VarMap.add v (l, l+1) bounds
          else bounds)
        stf.bounds
        VarMap.empty
    in
    { bounds ; formula = adjust_formula stf bounds}

  let widen left right =
    (* Printf.printf "%s WEDGE %s\n" (Formula.show srk left.formula) (Formula.show srk right.formula) ; *)
    let (bounds, lbounds, rbounds) =
      new_bounds (fun (ll, lu) (rl, ru) ->
          if ll <> rl || lu <> ru then
            (* Leave the one with a bigger distance unchanged *)
            if ru - rl > lu - ll then
              ((rl, ru), (rl, ru), (rl, ru))
            else ((ll, lu), (ll, lu), (ll, lu))
          else ((ll, lu), (ll, lu), (ll, lu)))
        left.bounds right.bounds
    in
    let to_wedge =
      let syms =
        VarMap.fold (fun v (l, u) m ->
            Symbol.Set.add (var_i_symbol v l) m
            |> Symbol.Set.add (var_i_symbol v u))
          bounds
          Symbol.Set.empty
      in
      let exists s = Symbol.Set.mem s syms in
      Wedge.abstract ~exists srk
    in
    let formula =
      Wedge.widen (to_wedge (adjust_formula left lbounds))
        (to_wedge (adjust_formula right rbounds))
      |> Wedge.to_formula
    in
    (* Printf.printf "Result: %s\n" (Formula.show srk formula) ; *)
    { bounds ; formula }

  let equal left right =
    VarMap.equal (=) left.bounds right.bounds
    (* todo: don't rely on transition.ml *)
    && T.equal (to_tr left) (to_tr right)

end
