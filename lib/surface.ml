open Common

(** Surface terms are the direct output from the parser. These use user-friendly
    explicit naming and distinguish top-level definitions from local let bindings. *)

type expr =
  | Var of name                                 (* x                            *)
  | Ann of expr * expr                          (* e : τ                        *)
  | Pi of name * expr * expr                    (* (a : A) → B                  *)
  | Lam of name * expr option * expr            (* λ x . e                      *)
  | Sig of (name * expr) list                   (* (x : A ; y : B ; z : C)      *)
  | Rcd of (name * expr) list                   (* (x = a , y = b , z = c)      *)
  | Prod of expr list                           (* (A ; B ; C)                  *)
  | Tup of expr list                            (* (a , b , c)                  *)
  | App of expr * expr                          (* a b                          *)
  | Proj of expr * name                         (* e.x                          *)
  | ProjAt of expr * int                        (* e.i                          *)
  | Let of name * expr option * expr * expr     (* let x : τ = e in e'          *)
  | Uni                                         (* Type                         *)
  | Bool                                        (* Bool                         *)
  | False                                       (* False                        *)
  | True                                        (* True                         *)
  | BoolInd of expr option * expr * expr * expr (* towards τ if e then a else b *)
  | Nat                                         (* ℕ                            *)
  | NatZ                                        (* Zero                         *)
  | NatS of expr                                (* Succ n                       *)
  | NatLit of int                               (* 0, 1, 2, 3, ...              *)
  | NatInd of expr * expr option                (* rec n at τ                   *)
    * expr * (name * name * expr)               (* | Zero . e₁ | Succ m, p . e₂ *)

and stmt =
  | Def of name * expr option * expr
  | Inf of expr
  | Eval of expr
  | Exec of expr
  | Check of expr * expr
  | Conv of expr * expr * expr
  | Parse of expr
  | Import of string

type prog = stmt list