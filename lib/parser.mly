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

%token EOF
%token INF EVAL EXEC

%token <string> IDENT
%token <int> NUM
%token LCURLY RCURLY LPAREN RPAREN COLON
%token RECORD SIG END
%token LAMBDA DOT ARROW
%token TOWARDS IF THEN ELSE
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

%type <prog> program
%type <stmt> statement
%type <expr> expr
%type <expr> atom

%type <expr> let_annot
%type <string * expr> lblval
%type <string * expr> lbltyp

%type <unit> lrcd
%type <unit> rrcd

%%
program:
  | stmts=list(statement); EOF { stmts }

statement:
  | DEF; x=IDENT; t=option(let_annot); EQ; e=expr; SEP { Def (x, t, e) }
  | INF; e=expr; SEP { Inf e }
  | EVAL; e=expr; SEP { Eval e }
  | EXEC; e=expr; SEP { Exec e }

expr:
  | es=nonempty_list(atom) { unfoldApp es }
  | e=expr; COLON; t=expr { Ann (e, t) }
  | a=expr; ARROW; b=expr { postprocessPi a b }

  | LAMBDA; xs=nonempty_list(IDENT); DOT; e=expr
  (** [LAMBDA] needs weak precedence to ensure `λx . e : t` == `λx . (e : t)` *)
    %prec WEAK { unfoldLam xs e }
  | TOWARDS; mtv=expr; IF; cond=expr; THEN; tc=expr; ELSE; fc=expr
    %prec WEAK { BoolInd (Some mtv, cond, tc, fc) }
  | IF; cond=expr; THEN; tc=expr; ELSE; fc=expr
    %prec WEAK { BoolInd (None, cond, tc, fc) }
  | LET; x=IDENT; t=option(let_annot); EQ; e=expr; IN; r=expr
    %prec WEAK { Let (x, t, e, r) }

%inline let_annot:
  | COLON; t=expr { t }

%inline ldict:
  | LCURLY { () }
  | RECORD { () }
%inline rdict:
  | rrcd { () }
%inline lrcd:
  | LCURLY { () }
  | SIG { () }
%inline rrcd:
  | RCURLY { () }
  | END { () }

atom:
  | x=IDENT { Var x }
  | LPAREN; e=expr; RPAREN { e }
  | LPAREN; t=expr; SEP; ts=separated_list(SEP, expr); RPAREN
    { postprocessProd (t::ts) }
  | LPAREN; e=expr; COMMA; es=separated_list(COMMA, expr); RPAREN
    { Tup (e::es) }
  | ldict; t=lblval; ts=list(lblval); rdict
    { Dict (t::ts) }
  | lrcd; t=lbltyp; ts=list(lbltyp); rrcd
    { Rcd (t::ts) }
  | e=atom; DOT; i=NUM { ProjAt (e, i) }
  | e=atom; DOT; i=IDENT { Proj (e, i) }
  | TYPE  { Uni }
  | BOOL  { Bool }
  | TRUE  { True }
  | FALSE { False }

%inline lblval:
  | l=IDENT; EQ; e=expr; SEP { (l, e) }
%inline lbltyp:
  | l=IDENT; COLON; e=expr; SEP { (l, e) }