%{
(** the [Surface] module contains our AST. *)
open Surface

(** abstract over type formers *)
type former = | FPi | FSig
let formerOf (f : former) (x, a, b) =
  match f with
  | FPi  -> Pi (x, a, b)
  | FSig -> Sig (x, a, b)

(** exception raised when a [nonempty_list] returns an empty list. *)
exception EmptyUnfolding

(** desugars `(x y z : a) → b` into `(x : a) → (y : a) → (z : a) → b`. *)
let rec unfoldFormer (f : former) (xs : string list) (dom : expr) (cod : expr) : expr =
  match xs with
  | [] -> raise EmptyUnfolding
  | [x] -> formerOf f (x, dom, cod)
  | x :: rest -> formerOf f (x, dom, unfoldFormer f rest dom cod)

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
let postprocessFormer (a : expr) (f : former) (b : expr) : expr =
  match a with
  | Ann (es, t) ->
    begin match appToVars es with
    | Some xs -> unfoldFormer f xs t b
    | None -> formerOf f ("", a, b)
    end
  | _ -> formerOf f ("", a, b)

%}

%token EOF

%token <string> IDENT
%token LPAREN RPAREN COLON
%token LAMBDA DOT ARROW
%token COMMA TIMES FST SND
%token TYPE BOOL TRUE FALSE
%token LET DEF EQ IN

%nonassoc WEAK
(** [ARROW]s are right-associative, [COLON]s require disambiguation *)
%nonassoc COLON
%right ARROW
(** subtlety: [COLON] must be higher than [ARROW], so that
    `x : a -> b` == `x : (a -> b)`
                 /= `(x : a) -> b` *)
%right TIMES


%start program

%type <expr> program
%type <expr> expr
%type <expr> atom

%type <Common.scope> scope
%type <former> former

%%
program:
  | e=expr; EOF { e }

expr:
  | es=nonempty_list(atom) { unfoldApp es }
  | e=expr; COLON; t=expr { Ann (e, t) }
  | a=expr; f=former; b=expr { postprocessFormer a f b }

  | LAMBDA; xs=nonempty_list(IDENT); DOT; e=expr
  (** [LAMBDA] needs weak precedence to ensure `λx . e : t` == `λx . (e : t)` *)
    %prec WEAK { unfoldLam xs e }
  | s=scope; x=IDENT; COLON; t=expr; EQ; e=expr; IN; r=expr
    %prec WEAK { Let (s, x, t, e, r) }

scope:
  | LET { Common.Loc }
  | DEF { Common.Top }

%inline former:
  | ARROW { FPi }
  | TIMES { FSig }

atom:
  | x=IDENT { Var x }
  | LPAREN; e=expr; RPAREN { e }
  | LPAREN; l=expr; COMMA; r=expr; RPAREN { Pair (l, r) }
  | e=atom; FST { Fst e }
  | e=atom; SND { Snd e }
  | TYPE  { Uni }
  | BOOL  { Bool }
  | TRUE  { True }
  | FALSE { False }