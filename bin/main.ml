module Sur = Myowntt.Surface

open Myowntt.Typecheck
open Myowntt.Pretty
open Myowntt.Lexer_old
open Myowntt.Eval

let exec (src : string) : unit =
  match parse_str src with
  | Ok ex ->
    print_endline (pretty_expr ex);
    let (trm, typ) = infer nullscene ex in
    print_endline (pretty_term trm);
    print_endline (": " ^ pretty_val typ);
    let vl = eval Emp trm in
    print_endline ("= " ^ pretty_val vl);
    print_endline ""
  | Error e -> print_endline e

let () =
  exec "Type";
  exec "let t : Type = Type in Type";
  exec "let typid  : Type -> Type = lam T . T in typid Bool";
  exec "let boolid : Bool -> Bool = lam x . x in boolid True";
  exec( "let id : (A : Type) -> A -> A = lam T . (lam x . x) in "
      ^ "id Bool False")