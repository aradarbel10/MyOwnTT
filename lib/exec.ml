open Common
open Pretty
open Typecheck
open Eval
open Lexer
open Conversion

let rec exec_stmt (scn : scene) (stmt : Sur.stmt) : scene =
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
  | Parse e ->
    print_endline ("successfully parsed " ^ pretty_expr e);
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
  | Import path -> _exec_file scn path


and exec (scn : scene) : (Sur.prog, string) result -> scene = function
  | Ok stmts ->
    List.fold_left exec_stmt scn stmts
  | Error e -> print_endline e; scn

and _exec_str scn str = exec scn (parse_str str)
and _exec_file scn file = exec scn (parse_file file)


let repl : unit =
  let rec aux (scn : scene) : unit =
    print_string "λΠ> ";
    let str = read_line () ^ ";" in
    if str = "#quit;" || str = "#q;" then () else
      let scn = exec scn (parse_str str) in
      aux scn
  in aux nullscene