open Common

(** Surface terms are the direct output from the parser. These use user-friendly
    explicit naming and distinguish top-level definitions from local let bindings. *)
type expr =
  | Var of name                              (* x                            *)
  | Ann of expr * expr                       (* e : τ                        *)
  | Pi of name * expr * expr                 (* (a : A) → B                  *)
  | Sig of name * expr * expr                (* (a : A) × B                  *)
  | Lam of name * expr                       (* λ x . e                      *)
  | Pair of expr * expr                      (* (a, b)                       *)
  | App of expr * expr                       (* a b                          *)
  | Fst of expr                              (* e.1                          *)
  | Snd of expr                              (* e.2                          *)
  | Let of scope * name * expr * expr * expr (* let x : τ = e in e'          *)
  | Uni                                      (* Type *)
  | Bool                                     (* bool                         *)
  | False                                    (* false                        *)
  | True                                     (* true                         *)
  | BoolInd of expr * expr * expr * expr     (* towards τ if e then a else b *)