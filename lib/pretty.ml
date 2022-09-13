open Common

module Syn = Syntax
module Sem = Semantics
module Sur = Surface

let rec pretty_expr (expr : Sur.expr) : string =
  match expr with
  | Var x -> x
  | Ann (e, t) -> "(" ^ pretty_expr e ^ " : " ^ pretty_expr t ^ ")"
  | Pi ("", a, b) -> "(" ^ pretty_expr a ^ " → " ^ pretty_expr b ^ ")"
  | Pi (x, a, b) -> "((" ^ x ^ " : " ^ pretty_expr a ^ ") → " ^ pretty_expr b ^ ")"
  (* TODO properly print singleton tuples and products *)
  | Rcd fs ->
    let entries = List.map (fun (lbl, typ) -> lbl ^ " : " ^ pretty_expr typ) fs in
    "(" ^ (String.concat "; " entries) ^ ")"
  | Prod ts ->
    let entries = List.map pretty_expr ts in
    "(" ^ (String.concat "; " entries) ^ ")"
  | Lam (x, e) -> "λ" ^ x ^ " . " ^ pretty_expr e
  | Dict fs ->
    let entries = List.map (fun (lbl, e) -> lbl ^ " = " ^ pretty_expr e) fs in
    "(" ^ (String.concat ", " entries) ^ ")"
  | Tup es ->
    let entries = List.map pretty_expr es in
    "(" ^ (String.concat ", " entries) ^ ")"
  | App (e1, e2) -> pretty_expr e1 ^ " " ^ pretty_expr e2
  | Proj (e, x) -> pretty_expr e ^ "." ^ x
  | ProjAt (e, i) -> pretty_expr e ^ "." ^ string_of_int i
  | Let (scp, x, t, e, rest) ->
    (match scp with | Loc -> "let " | Top -> "def ")
    ^ x ^ " : " ^ pretty_expr t ^ " = " ^ pretty_expr e
    ^ " in " ^ pretty_expr rest
  | Uni -> "Type"
  | Bool -> "Bool"
  | False -> "False"
  | True -> "True"
  | BoolInd (fam, e, t, f) ->
    "towards " ^ pretty_expr fam ^ " if " ^ pretty_expr e
    ^ " then " ^ pretty_expr t
    ^ " else " ^ pretty_expr f
  
let rec pretty_term_under (ns : name list) (e : Syn.term) : string =
  match e with
  | Var (Idx i) -> List.nth ns i
  (* TODO properly print parentheses around nested arrows (or other places where needed) *)
  | Pi ("", a, B b) -> "(" ^ pretty_term_under ns a ^ " → " ^ pretty_term_under (""::ns) b ^ ")"
  | Pi (x, a, B b) -> "((" ^ x ^ " : " ^ pretty_term_under ns a ^ ") → " ^ pretty_term_under (x::ns) b ^ ")"
  (* TODO properly print singleton tuples and products *)
  | Rcd fs ->
    let entries = snd @@ List.fold_left_map (fun ns (x, t) -> (x::ns, x ^ " : " ^ pretty_term_under ns t)) ns fs in
    "(" ^ (String.concat "; " entries) ^ ")"
  | Dict fs ->
    let entries = snd @@ List.fold_left_map (fun ns (x, e) -> (x::ns, x ^ " = " ^ pretty_term_under ns e)) ns fs in
    "(" ^ (String.concat ", " entries) ^ ")"
  | Prod ts ->
    let entries = List.map (pretty_term_under ns) ts in
    "(" ^ (String.concat "; " entries) ^ ")"
  | Tup es ->
    let entries = List.map (pretty_term_under ns) es in
    "(" ^ (String.concat ", " entries) ^ ")"
  (* TODO prettify folded lambdas *)
  | Lam (x, t, B e) -> "λ" ^ x ^ " : " ^ pretty_term_under ns t ^ " . " ^ pretty_term_under (x::ns) e
  | App (e1, e2) -> pretty_term_under ns e1 ^ " " ^ pretty_term_under ns e2
  | Proj (e, x) -> pretty_term_under ns e ^ "." ^ x
  | ProjAt (e, i) -> pretty_term_under ns e ^ "." ^ string_of_int i
  | Let (scp, x, t, e, B rest) ->
    (match scp with | Loc -> "let " | Top -> "def ")
    ^ x ^ " : " ^ pretty_term_under ns t ^ " = " ^ pretty_term_under ns e
    ^ " in " ^ pretty_term_under (x::ns) rest
  (*| Def (x, t, e, B rest) ->
    "def " ^ x ^ " : " ^ pretty_term_under ns t ^ " = " ^ pretty_term_under ns e
    ^ " in " ^ pretty_term_under (x::ns) rest*)
  | Uni -> "Type"
  | Bool -> "Bool"
  | False -> "False"
  | True -> "True"
  | BoolInd {motive; tcase; fcase; scrut} ->
    "towards " ^ pretty_term_under ns motive ^ " if " ^ pretty_term_under ns scrut
    ^ " then " ^ pretty_term_under ns tcase
    ^ " else " ^ pretty_term_under ns fcase

let pretty_term : Syn.term -> string = pretty_term_under []

(*
let pretty_val_under (ns : name list) (vl : Sem.value) : string =
  pretty_term_under ns (quote (Sem.Lvl (List.length ns)) vl)

let pretty_val : Sem.value -> string = pretty_val_under []
*)