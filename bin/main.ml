module Sur = Myowntt.Surface

open Myowntt.Typecheck
open Myowntt.Pretty
open Myowntt.Lexer
open Myowntt.Eval

let exec = function
  | Ok exs ->
    ignore @@ List.map (fun ex ->
    print_endline (pretty_expr ex);
    let (trm, typ) = infer nullscene ex in
    print_endline (pretty_term trm);
    print_endline (": " ^ pretty_term (quote (Lvl 0) typ));
    let vl = eval Emp trm in
    print_endline ("= " ^ pretty_term (quote (Lvl 0) vl));
    print_endline "";) exs
  | Error e -> print_endline e

let _exec_str str = exec (parse_str str)
let _exec_file file = exec (parse_file file)

let () =
  _exec_file "bin/examples/church-glue.own"
  (*
  exec_str "Type";
  exec_str "let t : Type = Type in Type";
  exec_str "let typid  : Type -> Type = lam T . T in typid Bool";
  exec_str "let boolid : Bool -> Bool = lam x . x in boolid True";
  exec_str ( "let id : (A : Type) -> A -> A = lam T . (lam x . x) in "
           ^ "id Bool False")
           *)