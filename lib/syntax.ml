open Common

type idx = Idx of int
(** Terms use indices (counting the environment from the right) for easy α-equivalence checking. *)

type term =
  | Var of idx
  | Pi of name * term * term binder
  | Sig of name * term * term binder
  | Lam of name * term * term binder
  | Pair of term * term
  | App of term * term
  | Fst of term
  | Snd of term
  | Let of name * term * term * term binder
  | Def of name * term * term * term binder
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