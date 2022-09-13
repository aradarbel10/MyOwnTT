open Common

type idx = Idx of int
(** Terms use indices (counting the environment from the right) for easy α-equivalence checking. *)

type term =
  | Var of idx
  | Pi of name * term * term binder
  | Lam of name * term * term binder
  | Rcd of (name * term) list
  | Dict of (name * term) list
  | Prod of term list
  | Tup of term list
  | App of term * term
  | Proj of term * name
  | ProjAt of term * int
  | Let of scope * name * term * term * term binder
  (*| Def of name * term * term * term binder*)
      (** We ditinguish local definitions [Let] from top level ones [Def].
          Only top level ones will be glued-evaluated. *)
  | Uni
      (** We use type-in-type axiom (a.k.a [Uni : Uni]). *)
  | Bool
  | True
  | False
  | BoolInd of {motive : term; tcase : term; fcase : term; scrut : term}
      (** When [motive] doesn't depend on its parameter,
          this is equivalent to if-then-else *)