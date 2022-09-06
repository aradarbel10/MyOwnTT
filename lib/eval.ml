open Common
module Syn = Syntax
module Sem = Semantics

(** Normalization-by-Evaluation
  NbE is a strategy for computing normal forms of terms, which we need for the
  conversion checking procedure described later.
  For a gentle introduction to NbE check out Favonia's video: https://youtu.be/atKqqiXslyo
  We rely on two main functions
  
  - eval  : term ---> value
    reduces all β redexes in the term to achieve a β-normal form
  - quote : value ---> term
    brings a normalized value back to the syntactic domain
  *)

exception IllTyped of string (** Used in points of the evaluator guaranteed by the typechecker to be unreachable *)

let rec eval (env : Sem.env) (tm : Syn.term) : Sem.value =
  match tm with
  | Var i -> Sem.atIdx env i
  | Pi (x, typ, bound) -> Pi (x, eval env typ, C {bdr = bound; env = env})
  | Sig (x, typ, bound) -> Sig (x, eval env typ, C {bdr = bound; env = env})
  | Lam (x, typ, bound) -> Lam (x, eval env typ, C {bdr = bound; env = env})
  | Pair (e1, e2) -> Pair (eval env e1, eval env e2)
  | App (e1, e2) -> vApp (eval env e1) (eval env e2)
  | Fst e -> vFst (eval env e)
  | Snd e -> vSnd (eval env e)
  | Let (x, _, body, B rest) ->
    let body' = eval env body in
    eval (Local (env, x, body')) rest
  | Def (x, body, typ, B rest) ->
    let typ' = eval env typ in
    let body' = lazy (eval env body) in
    let glue = Sem.Glue (Sem.height env, body') in
    let env' = Sem.Toplevel (env, x, Neut (glue, [], typ')) in
    eval env' rest
  | Uni -> Uni
  | Bool -> Bool
  | True -> True
  | False -> False
  | BoolInd {motive = mtv; tcase = tc; fcase = fc; scrut = scrut} ->
    let tc' = lazy (eval env tc) in
    let fc' = lazy (eval env fc) in
    (*  We evaluate each branch lazily in order to avoid redundant computations.
        Since we're implementing a pure lambda calculus it doesn't matter operationally, but might
        improve performace when there are big terms inside cases. *)
    let scrut' = eval env scrut in
    match scrut' with
    | True -> Lazy.force tc'
    | False -> Lazy.force fc'
    | Neut (hd, sp, Bool) ->
      let fam = Sem.C {bdr = B mtv; env = env} in
      let mtv' = eval env mtv in
      let elim = Sem.BoolInd {motive = mtv'; tcase = Lazy.force tc'; fcase = Lazy.force fc'} in
      let typ = inst fam scrut' in
      Neut (hd, elim :: sp, typ)
    | _ -> raise (IllTyped "can't eliminate non-bool")
    
(** Instantiate a closure(/type family) at given type *)
and inst (C {bdr = B body; env = env} : Sem.closure) (base : Sem.value) : Sem.value =
  eval (Local (env, "_x", base)) body
and instvar (C {bdr = _; env} as clos : Sem.closure) (typ : Sem.value) : Sem.value =
  inst clos (Neut (Var (Sem.height env), [], typ))
    
    
(** β-reduction helpers *)
and vApp (fnc : Sem.value) (arg : Sem.value) : Sem.value =
  match fnc with
  | Lam (_, _, body) -> inst body arg
  | Neut (hd, sp, Pi (_, base, fam)) ->
    let hd' = Sem.head_map (fun vl -> vApp vl arg) hd in
    let sp' = (Sem.App {arg = arg; base = base}) :: sp in
    Neut (hd', sp', inst fam base)
  | _ -> raise (IllTyped "can't apply on non-lambda")
and vFst (pr : Sem.value) : Sem.value =
  match pr with
  | Pair (v1, _) -> v1
  | Neut (hd, sp, Sig (_, base, _)) ->
    let hd' = Sem.head_map vFst hd in
    let sp' = Sem.Fst :: sp in
    Neut (hd', sp', base)
  | _ -> raise (IllTyped "can't project from non-pair")
and vSnd (pr : Sem.value) : Sem.value =
  match pr with
  | Pair (_, v2) -> v2
  | Neut (hd, sp, Sig (_, _, fam)) ->
    let fst = vFst pr in
    let hd' = Sem.head_map vSnd hd in
    let sp' = Sem.Snd :: sp in
    Neut (hd', sp', inst fam fst)
  | _ -> raise (IllTyped "can't project from non-pair")


let lvl2idx (Lvl siz : Sem.lvl) (Lvl i : Sem.lvl) = Syn.Idx (siz - i - 1)

let rec quote (siz : Sem.lvl) (vl : Sem.value) : Syn.term =
  match vl with
  | Pi (x, a, b) ->
    let fam = inst b (Sem.var siz a) in
    Pi (x, quote siz a, B (quote (Sem.inc siz) fam))
  | Sig (x, a, b) ->
    let fam = inst b (Sem.var siz a) in
    Sig (x, quote siz a, B (quote (Sem.inc siz) fam))
  | Lam (x, t, e) ->
    let fam = inst e (Sem.var siz t) in
    Lam (x, quote siz t, B (quote (Sem.inc siz) fam))
  | Uni -> Uni
  | Bool -> Bool
  | True -> True
  | False -> False
  | Pair (e1, e2) -> Pair (quote siz e1, quote siz e2)
  | Neut (hd, sp, _) -> quote_neut siz hd sp


and quote_neut (siz : Sem.lvl) (hd : Sem.head) (sp : Sem.spine) : Syn.term =
  List.fold_right (quote_elim siz) sp (quote_head siz hd)

and quote_elim (siz : Sem.lvl) (em : Sem.elim) (scrut : Syn.term) : Syn.term =
  match em with
  | Fst -> Fst scrut
  | Snd -> Snd scrut
  | App {arg; _} ->
    let arg = quote siz arg in
    App (scrut, arg)
  | BoolInd {motive; tcase; fcase} ->
    let motive = quote siz motive in
    let tcase = quote siz tcase in
    let fcase = quote siz fcase in
    BoolInd {motive = motive; tcase = tcase; fcase = fcase; scrut = scrut}

and quote_head (siz : Sem.lvl) (hd : Sem.head) : Syn.term =
  match hd with
  | Var i | Glue (i, _) -> Var (lvl2idx siz i)