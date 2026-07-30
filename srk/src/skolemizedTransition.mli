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
     end)
    (VarMap : BatMap.S with type key = Var.t)
    (W : sig
       val wt : int * int -> T.t
       val length : Pathexpr.nested Pathexpr.t -> int VarMap.t
       val guess_vars : Pathexpr.nested Pathexpr.t -> (int * int) VarMap.t
    end) : sig

  val transition : Pathexpr.nested Pathexpr.t -> T.t

end
