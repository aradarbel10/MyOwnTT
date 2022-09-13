%{
(** the [Surface] module contains our AST. *)
open Surface

(** exception raised when a [nonempty_list] returns an empty list. *)
exception EmptyUnfolding

(** desugars `(x y z : a) → b` into `(x : a) → (y : a) → (z : a) → b`. *)
let rec unfoldPi (xs : string list) (dom : expr) (cod : expr) : expr =
  match xs with
  | [] -> raise EmptyUnfolding
  | [x] -> Pi (x, dom, cod)
  | x :: rest -> Pi (x, dom, unfoldPi rest dom cod)

(** unfolds a nonempty list of expressions to their correctly-associated application. *)
let rec unfoldApp (es : expr list) : expr =
  match es with
  | [] -> raise EmptyUnfolding
  | [e] -> e
  | e1 :: e2 :: rest -> unfoldApp ((App (e1, e2)) :: rest)

(** unfolds lambda abstractions with multiple parameters *)
let rec unfoldLam (xs : string list) (e : expr) : expr =
  match xs with
  | [] -> raise EmptyUnfolding
  | [x] -> Lam (x, e)
  | x :: rest -> Lam (x, unfoldLam rest e)

(** converts an application of the form `(((w x) y ) z)` of variables
    to a list of variable names. returns [None] if any of the expressions are not a variable. *)
let rec appToVars (es : expr) : (string list) option =
  match es with
  | Var x -> Some [x]
  | App (rest, Var x) ->
    begin match appToVars rest with
    | None -> None
    | Some xs -> Some (xs @ [x])
    end
  | _ -> None

(** if the LHS of an arrow is an application of variables with an annotation,
    desugar it using [unfoldPi]. in any other case treat it as a non-dependent arrow. *)
let postprocessPi (a : expr) (b : expr) : expr =
  match a with
  | Ann (es, t) ->
    begin match appToVars es with
    | Some xs -> unfoldPi xs t b
    | None -> Pi ("", a, b)
    end
  | _ -> Pi ("", a, b)

let postprocessProd (es : expr list) : expr =
  let rec aux (es : expr list) : (string * expr) list option =
    match es with
    | [] -> Some []
    | Ann (Var l, t) :: rest ->
      begin match aux rest with
      | None -> None
      | Some fs -> Some ((l, t)::fs)
      end
    | _ -> None
  in match aux es with
  | Some fs -> Rcd fs
  | None -> Prod es

%}

%token HLINE EOF

%token <string> IDENT
%token <int> NUM
%token LPAREN RPAREN COLON
%token LAMBDA DOT ARROW
%token COMMA SEP
%token TYPE BOOL TRUE FALSE
%token LET DEF EQ IN

%nonassoc WEAK
(** [ARROW]s are right-associative, [COLON]s require disambiguation *)
%nonassoc COLON
%right ARROW
(** subtlety: [COLON] must be higher than [ARROW], so that
    `x : a -> b` == `x : (a -> b)`
                 /= `(x : a) -> b` *)


%start program

%type <expr list> program
%type <expr> expr
%type <expr> atom

%type <Common.scope> scope
%type <string * expr> lblval

%%
program:
  | es=separated_nonempty_list(HLINE, expr); EOF { es }

expr:
  | es=nonempty_list(atom) { unfoldApp es }
  | e=expr; COLON; t=expr { Ann (e, t) }
  | a=expr; ARROW; b=expr { postprocessPi a b }

  | LAMBDA; xs=nonempty_list(IDENT); DOT; e=expr
  (** [LAMBDA] needs weak precedence to ensure `λx . e : t` == `λx . (e : t)` *)
    %prec WEAK { unfoldLam xs e }
  | s=scope; x=IDENT; COLON; t=expr; EQ; e=expr; IN; r=expr
    %prec WEAK { Let (s, x, t, e, r) }

scope:
  | LET { Common.Loc }
  | DEF { Common.Top }

atom:
  | x=IDENT { Var x }
  | LPAREN; e=expr; RPAREN { e }
  | LPAREN; t=expr; SEP; ts=separated_list(SEP, expr); RPAREN
    { postprocessProd (t::ts) }
  | LPAREN; e=expr; COMMA; es=separated_list(COMMA, expr); RPAREN
    { Tup (e::es) }
  | LPAREN; t=lblval; COMMA; ts=separated_list(COMMA, lblval); RPAREN
    { Dict (t::ts) }
  | e=atom; DOT; i=NUM { ProjAt (e, i) }
  | e=atom; DOT; i=IDENT { Proj (e, i) }
  | TYPE  { Uni }
  | BOOL  { Bool }
  | TRUE  { True }
  | FALSE { False }

lblval:
  | l=IDENT; EQ; e=expr { (l, e) }