open Common
open Eval

module Syn = Syntax
module Sem = Semantics
module Sur = Surface

let rec pretty_expr (expr : Sur.expr) : string =
  match expr with
  | Var x -> x
  | Ann (e, t) -> "(" ^ pretty_expr e ^ " : " ^ pretty_expr t ^ ")"
  | Pi ("", a, b) -> "(" ^ pretty_expr a ^ " → " ^ pretty_expr b ^ ")"
  | Pi (x, a, b) -> "(" ^ x ^ " : " ^ pretty_expr a ^ ") → " ^ pretty_expr b
  | Sig ("", a, b) -> pretty_expr a ^ " × " ^ pretty_expr b
  | Sig (x, a, b) -> "(" ^ x ^ " : " ^ pretty_expr a ^ ") × " ^ pretty_expr b
  | Lam (x, e) -> "(λ" ^ x ^ " . " ^ pretty_expr e ^ ")"
  | Pair (e1, e2) -> "(" ^ pretty_expr e1 ^ ", " ^ pretty_expr e2 ^ ")"
  | App (e1, e2) -> "(" ^ pretty_expr e1 ^ " " ^ pretty_expr e2 ^ ")"
  | Fst e -> pretty_expr e ^ ".1"
  | Snd e -> pretty_expr e ^ ".2"
  | Let (_, x, t, e, rest) ->
    "let " ^ x ^ " : " ^ pretty_expr t ^ " = " ^ pretty_expr e
    ^ " in " ^ pretty_expr rest
  | Uni -> "Type"
  | Bool -> "Bool"
  | False -> "False"
  | True -> "True"
  | BoolInd (fam, e, t, f) ->
    "towards " ^ pretty_expr fam ^ " if " ^ pretty_expr e
    ^ " then " ^ pretty_expr t
    ^ " else " ^ pretty_expr f

let pretty_term : Syn.term -> string =
  let rec aux (ns : name list) (e : Syn.term) : string =
    match e with
    | Var (Idx i) -> List.nth ns i
    | Pi ("", a, B b) -> aux ns a ^ " → " ^ aux (""::ns) b
    | Pi (x, a, B b) -> "(" ^ x ^ " : " ^ aux ns a ^ ") → " ^ aux (x::ns) b
    | Sig ("", a, B b) -> aux ns a ^ " × " ^ aux (""::ns) b
    | Sig (x, a, B b) -> "(" ^ x ^ " : " ^ aux ns a ^ ") × " ^ aux (x::ns) b
    | Lam (x, t, B e) -> "λ" ^ x ^ " : " ^ aux ns t ^ " . " ^ aux (x::ns) e
    | Pair (e1, e2) -> "(" ^ aux ns e1 ^ ", " ^ aux ns e2 ^ ")"
    | App (e1, e2) -> aux ns e1 ^ " " ^ aux ns e2
    | Fst e -> aux ns e ^ ".1"
    | Snd e -> aux ns e ^ ".2"
    | Let (x, t, e, B rest) ->
      "let " ^ x ^ " : " ^ aux ns t ^ " = " ^ aux ns e
      ^ " in " ^ aux (x::ns) rest
    | Def (x, t, e, B rest) ->
      "def " ^ x ^ " : " ^ aux ns t ^ " = " ^ aux ns e
      ^ " in " ^ aux (x::ns) rest
    | Uni -> "Type"
    | Bool -> "Bool"
    | False -> "False"
    | True -> "True"
    | BoolInd {motive; tcase; fcase; scrut} ->
      "towards " ^ aux ns motive ^ " if " ^ aux ns scrut
      ^ " then " ^ aux ns tcase
      ^ " else " ^ aux ns fcase
  in aux []

let pretty_val (vl : Sem.value) : string =
  pretty_term (quote (Sem.Lvl 0) vl)