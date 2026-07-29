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
       val mul : t -> t -> t
       val add : t -> t -> t
       val domain : (C.t Iteration.exp_op) ref
       val equal : t -> t -> bool
     end) : sig

  type t

  (** Convert a T.t to a skolemized transition formula with the given
      variable bounds. *)
  val of_tr : T.t -> (Var.t * (int * int)) BatEnum.t -> t

  (** Convert to a T.t *)
  val to_tr : t -> T.t

  (** Sequentially compose two transitions. This is fast on operands
      whose bounds only intersect in the middle. *)
  val mul : t -> t -> t

  (** Non-deterministically choose between two transitions. This is
      fast on operands whose bounds are the same. *)
  val add : t -> t -> t

  (** Unexecutable transition (unit of [add]). *)  
  val zero : t

  (** Skip (unit of [mul]). *)
  val one : t

  (** Overapproximate the reflexive transitive closure. *)
  val star : t -> t

  (** Project out all local variables *)
  val project : t -> t

  (** Widen (see transition.ml) *)
  val widen : t -> t -> t

  (** Test whether two transitions are equal up to logical equivalence
      and renaming skolem constants. *)
  val equal : t -> t -> bool

end
