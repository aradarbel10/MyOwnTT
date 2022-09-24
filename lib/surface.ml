open Common

(** Surface terms are the direct output from the parser. These use user-friendly
    explicit naming and distinguish top-level definitions from local let bindings. *)

type stmt =
  | Def of name * expr option * expr
  | Inf of expr
  | Eval of expr
  | Exec of expr

and expr =
  | Var of name                                 (* x                            *)
  | Ann of expr * expr                          (* e : τ                        *)
  | Pi of name * expr * expr                    (* (a : A) → B                  *)
  | Lam of name * expr                          (* λ x . e                      *)
  | Rcd of (name * expr) list                   (* (x : A ; y : B ; z : C)      *)
  | Dict of (name * expr) list                  (* (x = a , y = b , z = c)      *)
  | Prod of expr list                           (* (A ; B ; C)                  *)
  | Tup of expr list                            (* (a , b , c)                  *)
  | App of expr * expr                          (* a b                          *)
  | Proj of expr * name                         (* e.x                          *)
  | ProjAt of expr * int                        (* e.i                          *)
  | Let of name * expr option * expr * expr     (* let x : τ = e in e'          *)
  | Uni                                         (* Type                         *)
  | Bool                                        (* bool                         *)
  | False                                       (* false                        *)
  | True                                        (* true                         *)
  | BoolInd of expr option * expr * expr * expr (* towards τ if e then a else b *)

type prog = stmt list