open Common

open Eval
open Conversion
open Pretty

module Sur = Surface
module Syn = Syntax
module Sem = Semantics


(** While environments assign values for variables, contexts store types.
    In our case both are represented the same way but we still give them different names. *)
type ctx = (name * Sem.value) list

let lookupVar (x : name) (ctx : ctx) =
  let rec aux (i : int) (x : name) (ctx : ctx) : (Syn.idx * Sem.value) = 
    match ctx with
    | [] -> raise Sem.OutOfBounds
    | (x', typ) :: ctx' ->
      if x = x' then (Syn.Idx i, typ) else aux (i + 1) x ctx'
  in aux 0 x ctx
    
(** Bidirectional Type Checking *)
type scene = {ctx : ctx; env : Sem.env; hi : Sem.lvl}
let nullscene = {ctx = []; env = Emp; hi = Lvl 0}
    
let assume (x : name) (typ : Sem.value) (scn : scene) : scene =
  { ctx = (x, typ) :: scn.ctx; env = Local (scn.env, x, Sem.var scn.hi typ); hi = Sem.inc scn.hi }
    
let define (scp : scope) (x : name) (typ : Sem.value) (vl : Sem.value) (scn : scene) : scene =
  let extend = match scp with
  | Loc -> Sem.Local (scn.env, x, vl)
  | Top -> Sem.Toplevel (scn.env, x, vl)
  in { ctx = (x, typ) :: scn.ctx; env = extend; hi = Sem.inc scn.hi }
    
exception UnInferrable
exception TypeError of string
    
let rec infer (scn : scene) (expr : Sur.expr) : Syn.term * Sem.value =
  match expr with
  | Var x -> let (i, typ) = lookupVar x scn.ctx in (Var i, typ)
  | Pi (x, a, b) ->
    let a  = check scn a Sem.Uni in
    let va = eval scn.env a in
    let b  = check (assume x va scn) b Sem.Uni in
    (Pi (x, a, B b), Uni)
  | Sig (x, a, b) ->
    let a  = check scn a Sem.Uni in
    let va = eval scn.env a in
    let b  = check (assume x va scn) b Sem.Uni in
    (Sig (x, a, B b), Uni)
  | Ann (e, typ) ->
    let typ = check scn typ Uni in
    let typ = eval scn.env typ in
    let e   = check scn e typ in
    (e, typ)
  | Fst pr ->
    let (pr, typ) = infer scn pr in
    begin match typ with
    | Sig (_, a, _) -> (Fst pr, a)
    | _ -> raise (TypeError "can't project from a non-pair type")
    end
  | Snd pr ->
    let (pr, typ) = infer scn pr in
    begin match typ with
    | Sig (_, _, b) ->
      let fst = eval scn.env (Fst pr) in
      let fam = inst b fst in
      (Snd pr, fam)
    | _ -> raise (TypeError "can't project from a non-pair type")
    end
  | App (e1, e2) ->
    let (e1, t1) = infer scn e1 in begin
    match t1 with
    | Pi (_, a, b) ->
      let e2 = check scn e2 a in
      let ve2 = eval scn.env e2 in
      let fam = inst b ve2 in
      (App (e1, e2), fam)
    | _ -> raise (TypeError ("can't apply on a non-function type " ^ pretty_term e1))
    end
  | Let (scp, x, typ, e, rest) ->
    let (bdr, scn) = checkLet scn scp x typ e in
    let (rest, resttyp) = infer scn rest in
    (bdr rest, resttyp)
  | Uni -> (Uni, Uni)
  | Bool -> (Bool, Uni)
  | True -> (True, Bool)
  | False -> (False, Bool)
  | BoolInd (mtv, scrut, tc, fc) ->
    let scrut = check scn scrut Bool in
    let vscrut = eval scn.env scrut in
    let mtv = check scn mtv (Sem.Pi ("dum", Bool, C {bdr = B Uni; env = Emp})) in
    let vmtv = eval scn.env mtv in
    let typ = vApp vmtv vscrut in
    let tc = check scn tc typ in
    let fc = check scn fc typ in
    let ind = Syn.BoolInd {motive = mtv; tcase = tc; fcase = fc; scrut = scrut} in
    (ind, typ)
  | _ -> raise UnInferrable

and check (scn : scene) (expr : Sur.expr) (typ : Sem.value) : Syn.term =
  match expr, typ with
  | Lam (x, e), Pi (_, a, b) ->
    let fam = instvar b a in
    let e = check (assume x a scn) e fam in
    Lam (x, quote scn.hi a, B e)
  | Pair (e1, e2), Sig (_, a, b) ->
    let e1 = check scn e1 a in
    let ve1 = eval scn.env e1 in
    let b = inst b ve1 in
    let e2 = check scn e2 b in
    Pair (e1, e2)
  | Let (scp, x, typ, e, rest), resttyp ->
    let (bdr, scn) = checkLet scn scp x typ e in
    let rest = check scn rest resttyp in
    bdr rest
  | expr, expected ->
    let (expr, actual) = infer scn expr in
    try
      conv scn.hi expected actual Uni;
      expr
    with
      | UnEq s -> raise (TypeError ("inferred type doesn't match expected type, because: " ^ s))

and checkLet (scn : scene) (scp : scope) (x : name) (typ : Sur.expr) (e : Sur.expr) : (Syn.term -> Syn.term) * scene =
  let typ = check scn typ Uni in
  let vtyp = eval scn.env typ in
  let e = check scn e vtyp in
  let ve = eval scn.env e in
  ((fun rest -> Let (x, typ, e, B rest)), define scp x vtyp ve scn)