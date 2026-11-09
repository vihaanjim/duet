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
       val typ : t -> typ_fo
       val symbol_of : t -> symbol
       val is_global : t -> bool
       val compare : t -> t -> int
     end)
    (T : sig
       type t
       type var = Var.t
       val construct : C.t formula -> (var * C.t term) list -> t
       val guard : t -> C.t formula
       val mem_transform : var -> t -> bool
       val get_transform : var -> t -> (C.t, typ_fo) expr
       val defines : t -> var list
       val uses : t -> var list
       val zero : t
       val one : t
       val star : t -> t
       val exists : (Var.t -> bool) -> t -> t
     end)
= struct

  module VarMap = BatMap.Make(Var)
  module VarSet = BatSet.Make(Var)

  module IntPair = struct
    type t = int * int [@@deriving ord]
    let equal (x,y) (x',y') = (x=x' && y=y')
    let hash = Hashtbl.hash
  end
  module HT = BatHashtbl.Make(IntPair)
  module CallSet = BatSet.Make(IntPair)

  type edge_weight =
    | Transition of T.t
    | Call of int * int

  type query =
    { weight    : int -> int -> edge_weight;
      length    : Pathexpr.nested Pathexpr.t -> int VarMap.t;
      length_to : int -> int VarMap.t;
      table     : (C.t formula * (int * int) VarMap.t) Pathexpr.Table.t;
      summaries : T.t HT.t;
      query     : WeightedGraph.RecGraph.query }

  let mk_query ~weight rg v =
    let query = WeightedGraph.RecGraph.mk_query rg v in
    (* Compute the `length` of a path expression. This is simply
       the number of times that each variable is defined in the
       expression *)
    let length_algebra weight_query =
      let union f = VarMap.union (fun _ a b -> Some (f a b)) in
      function
      | `Edge (u, v) ->
         begin match weight u v with
         | Transition tr ->
            List.fold_left (fun m v ->
                if not (VarMap.mem v m) then VarMap.add v 0 m
                else m)
              (List.fold_left (fun m v -> VarMap.add v 1 m)
                 VarMap.empty
                 (T.defines tr))
              (T.uses tr)
         | Call (en,ex) ->
            WeightedGraph.RecGraph.get_summary
              (Option.get weight_query) (en,ex)
         end
      | `Mul (l1, l2) -> union (+) l1 l2
      | `Add (l1, l2) -> union Stdlib.Int.max l1 l2
      | `Star l -> VarMap.map (fun d -> if d = 0 then 0 else 1) l
      | `Segment l ->
         VarMap.filter_map (fun v d ->
             if Var.is_global v then
               if d = 0 then Some 0 else Some 1
             else None) l
      | `One | `Zero -> VarMap.empty
    in
    let module LengthAbstractWeight = struct
        type weight = int VarMap.t
        type abstract_weight = VarSet.t

        let abstract map = VarMap.keys map |> VarSet.of_enum
        let concretize set = VarSet.fold (fun v -> VarMap.add v 1) set VarMap.empty
        let equal = VarSet.equal
        let widen = VarSet.union
      end
    in
    let length_query =
      WeightedGraph.RecGraph.summarize_iterative query
        (length_algebra None)
        ~delay:0
        (module LengthAbstractWeight)
    in
    let length = 
        let algebra = length_algebra (Some length_query) in
        let table = Pathexpr.mk_table () in
        Pathexpr.eval_nested ~table ~algebra
    in
    let length_to = WeightedGraph.RecGraph.path_weight length_query in
    let summaries = HT.create 991 in
    { weight; length; length_to; query; summaries;
      table = Pathexpr.Table.create 991; }

  let srk = C.context

  (* Canonical name for the ith version of a variable *)
  let var_i_symbol =
    Memo.memo (fun (v, i) ->
        if i = 0 then Var.symbol_of v
        else
          mk_symbol srk
            ~name:(Var.show v ^ string_of_int i)
            (Var.typ v :> typ))
  let ith_copy i v = mk_const srk (var_i_symbol (v, i))

  let of_tr vars tr =
    let subst =
      VarMap.fold (fun var (l, _) ->
          Symbol.Map.add (Var.symbol_of var) (ith_copy l var))
        vars
        Symbol.Map.empty
    in
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol srk sym in
          let typ = typ_symbol srk sym in
          mk_const srk (mk_symbol srk ~name typ))
    in
    let sigma s =
      match Symbol.Map.find_opt s subst with
      | Some t -> t
      | None -> fresh_skolem s
    in
    let post_defs =
      VarMap.fold (fun var (l, u) post_defs ->
          (* We need to include a set expression if this variable is
             transformed, or otherwise if l and u are different (to
             make sure that x_l = x_u) *)
          if T.mem_transform var tr then
            (mk_eq srk (ith_copy u var)
               (substitute_const srk sigma (T.get_transform var tr))
            )::post_defs
          else if l <> u then
            (mk_eq srk (ith_copy u var) (ith_copy l var))::post_defs
          else post_defs)
        vars
        []
    in
    mk_and srk ((substitute_const srk sigma (T.guard tr))::post_defs)
    |> rewrite srk ~up:(SrkSimplify.simplify_terms_rewriter srk % Nonlinear.simplify_terms_rewriter srk)
  
  let to_tr vars phi =
    let (transform, subst) =
      VarMap.fold (fun v (l, u) (transform, subst) ->
          ((if l = u then transform else (v, (ith_copy u v))::transform),
           Symbol.Map.add (var_i_symbol (v, l)) (mk_const srk (Var.symbol_of v)) subst))
        vars
        ([], Symbol.Map.empty)
    in
    T.construct (substitute_map srk subst (phi)) transform

  let rec f q pe vars =
    (* Printf.printf "%s(%d-%d) %s\n" (VarMap.choose vars |> fst |> Var.show) (VarMap.choose vars |> snd |> fst) (VarMap.choose vars |> snd |> snd) (Pathexpr.show pe) ; *)
    if Pathexpr.Table.mem q.table pe then
      let (phi, vars') = Pathexpr.Table.find q.table pe in
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
        to_tr vars' phi |> of_tr vars
    else
      let res =
        match Pathexpr.destruct pe with
        | `Edge (u, v) ->
           begin match q.weight u v with
           | Transition tr -> tr
           | Call (en,ex) -> HT.find q.summaries (en,ex)
           end |> of_tr vars
        | `Mul (left, right) ->
           let left_vars =
             VarMap.merge (fun _ lu d ->
                 match lu, d with
                 | Some (l, _), Some d -> Some (l, l+d)
                 | _ -> None)
               vars (q.length left)
           in
           let right_vars =
             VarMap.merge (fun _ lu d ->
                 match lu, d with
                 | Some (l, u), Some d -> Some (l+d, u)
                 | Some (l, u), None -> Some (l, u)
                 | _ -> None)
               vars (q.length left)
           in
           mk_and srk [f q left left_vars ; f q right right_vars]
        | `Add (left, right) ->
           mk_or srk [f q left vars ; f q right vars]
        | `Star pe' ->
           let len = q.length pe' in
           let vars' =
             VarMap.mapi (fun v (l, u) ->
                 let d = VarMap.find_default 0 v len in
                 if d = 0 then (l, u) else (l+1, l+1+d))
               vars
           in
           f q pe' vars' |> to_tr vars' |> T.star |> of_tr vars
        | `Segment pe' ->
           let vars' =
             VarMap.merge (fun _ lu d ->
                 match lu, d with
                 | Some (l, u), _ -> Some (l, u)
                 | None, Some d -> Some (0, d)
                 | _ -> assert false)
               vars
               (q.length pe')
           in
           f q pe' vars' |> to_tr vars' |> T.exists Var.is_global
           |> of_tr vars
        | `One ->
           VarMap.fold (fun var (l, u) lst ->
               if l <> u then
                 (mk_eq srk (ith_copy l var) (ith_copy u var))::lst
               else lst)
             vars []
           |> mk_and srk
        | `Zero -> mk_false srk
      in
      Pathexpr.Table.add q.table pe (res, vars) ;
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
  
  let transition q pe =
    match Pathexpr.destruct pe with
    | `Zero -> T.zero
    | `One -> T.one
    | _ ->
       (* Guess which variables to use (this is always correct on
          reducible flow graphs!) *)
       let pre = match src pe with
         | Some s -> q.length_to s
         | None -> VarMap.empty
       in
       let vars =
         VarMap.merge (fun _ l d ->
                let l = Option.value ~default:0 l in
                let d = Option.value ~default:0 d in
                Some (l, l + d))
           pre (q.length pe)
       in
       f q pe vars |> to_tr vars

  let summarize_iterative
        ~weight rg v
        ?(delay=1)
        (module A : WeightedGraph.AbstractWeight with type weight = T.t) =
    let query = mk_query ~weight rg v in
    (* Machinery copied over from weightedGraph.ml. *)
    let module RG = WeightedGraph.RecGraph in
    let changed = ref CallSet.empty in
    let set_summary call weight =
      changed := CallSet.add call !changed;
      HT.replace query.summaries call weight
    in
    let summarize call =
      let pe = RG.call_pathexpr query.query call
               |> Pathexpr.promote in
      if not (CallSet.is_empty !changed) then
        Pathexpr.Table.forget query.table (fun u v ->
            match query.weight u v with
            | Transition _ -> true
            | Call (en,ex) ->
               not (CallSet.mem (en,ex) !changed)) ;
      changed := CallSet.empty ;
      transition query pe
      |> T.exists Var.is_global
    in
    let callgraph = RG.mk_callgraph query.query in
    let abstract_summaries = HT.create 991 in
    (* stabilize summaries within a WTO component, and add to unstable
       all calls whose summary (may have) changed as a result. *)
    let rec fix = function
      | `Vertex call ->
         summarize call
         |> set_summary call
      | `Loop loop ->
         let header = RG.CallGraphLoop.header loop in
         let rec fix_component delay =
           let old_abs_weight = HT.find abstract_summaries header in
           let (new_abs_weight, new_weight) =
             let new_weight = summarize header in
             let new_abs_weight = A.abstract new_weight in
             if delay > 0 then
               (new_abs_weight, new_weight)
             else
               let new_abs_weight = A.widen old_abs_weight new_abs_weight in
               let new_weight = A.concretize new_abs_weight in
               (new_abs_weight, new_weight)
           in
           HT.replace abstract_summaries header new_abs_weight;
           set_summary header new_weight;
           List.iter fix (RG.CallGraphLoop.children loop);
           if not (A.equal old_abs_weight new_abs_weight)
           then fix_component (delay - 1)
         in
         fix_component delay
    in
    let abstract_zero = A.abstract T.zero in
    callgraph
    |> RG.CallGraph.iter_vertex (fun call ->
           set_summary call T.zero;
           HT.add abstract_summaries call abstract_zero);
    List.iter fix (RG.CallGraphLoop.loop_nest callgraph);
    query

  let path_weight query tgt =
    WeightedGraph.RecGraph.pathexpr query.query tgt
    |> transition query

  let call_weight query call =
    WeightedGraph.RecGraph.call_pathexpr query.query call
    |> Pathexpr.promote
    |> transition query

  let omega_path_weight query omega_algebra =
    let omega_table = Pathexpr.OmegaTable.create 991 in
    let paths = WeightedGraph.RecGraph.omega_pathexpr query.query in
    let rec f_omega oe =
      if Pathexpr.OmegaTable.mem omega_table oe then
        Pathexpr.OmegaTable.find omega_table oe
      else
        let res =
          begin match Pathexpr.destruct_omega oe with
          | `Omega pe -> `Omega (transition query pe)
          | `Mul (pe, oe') -> `Mul (transition query pe, f_omega oe')
          | `Add (oe1, oe2) -> `Add (f_omega oe1, f_omega oe2)
          end |> omega_algebra
        in
        Pathexpr.OmegaTable.add omega_table oe res ;
        res
    in
    f_omega paths

end
