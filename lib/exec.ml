open Common
open Pretty
open Typecheck
open Eval
open Lexer
open Conversion

let exec_stmt (scn : scene) (stmt : Sur.stmt) : scene =
  match stmt with
  | Def (x, t, e) ->
    snd (checkLet scn Top x t e)
  | Inf e ->
    let (_, t) = infer scn e in
    let names = List.map fst scn.ctx in
    print_endline ("the type of " ^ pretty_expr e ^
      " is " ^ pretty_term_under names (quote (scn.hi) t) ^ "\n");
    scn
  | Eval e ->
    let (e', _) = infer scn e in
    let vl = eval scn.env e' in
    let names = List.map fst scn.ctx in
    print_endline ("the normal form of " ^ pretty_expr e
      ^ " is " ^ pretty_term_under names (quote (scn.hi) vl) ^ "\n");
    scn
  | Exec e ->
    let (e', t) = infer scn e in
    let names = List.map fst scn.ctx in
    let vl = eval scn.env e' in
    print_endline ("the type of " ^ pretty_expr e ^
      " is " ^ pretty_term_under names (quote (scn.hi) t));
    print_endline ("its direct elaboration is " ^ pretty_term_under names e');
    print_endline ("and its normal form is " ^ pretty_term_under names (quote (scn.hi) vl) ^ "\n");
    scn
  | Check (e, t) ->
    let t' = check scn t Uni in
    let vt = eval scn.env t' in
    let e = check scn e vt in
    let names = List.map fst scn.ctx in
    print_endline ("the expression " ^ pretty_term_under names e);
    print_endline ("successfully checked against type " ^ pretty_term_under names t' ^ "\n");
    scn
    | Conv (e1, e2, t) ->
    let t' = check scn t Uni in
    let vt = eval scn.env t' in
    let e1' = check scn e1 vt in
    let ve1 = eval scn.env e1' in
    let e2' = check scn e2 vt in
    let ve2 = eval scn.env e2' in
    let names = List.map fst scn.ctx in
    conv scn.hi ve1 ve2 vt;
    print_endline ("the expression " ^ pretty_term_under names e1');
    print_endline ("and " ^ pretty_term_under names e2');
    print_endline ("are definitionally equal at " ^ pretty_term_under names t' ^ "\n");
    scn


let exec : (Sur.prog, string) result -> unit = function
  | Ok stmts ->
    ignore @@ List.fold_left exec_stmt nullscene stmts
  | Error e -> print_endline e

let _exec_str str = exec (parse_str str)
let _exec_file file = exec (parse_file file)