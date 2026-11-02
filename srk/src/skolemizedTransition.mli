(** Skolemized transition formulas. *)
open Syntax

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
     end) : sig

  type query

  type edge_weight =
    | Transition of T.t
    | Call of int * int

  val summarize_iterative : weight:(int -> int -> edge_weight) ->
                            WeightedGraph.RecGraph.t ->
                            int ->
                            ?delay:int ->
                            (module WeightedGraph.AbstractWeight
                                    with type weight = T.t) ->
                            query

  val path_weight : query -> WeightedGraph.vertex -> T.t

  val call_weight : query -> WeightedGraph.RecGraph.call -> T.t
  val omega_path_weight : query -> (T.t,'b) Pathexpr.omega_algebra -> 'b

end
