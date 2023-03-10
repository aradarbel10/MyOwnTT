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
    | [] -> raise (Sem.OutOfBounds x) (* TODO raise UndefinedName *)
    | (x', typ) :: ctx' ->
      if x = x' then (Syn.Idx i, typ) else aux (i + 1) x ctx'
  in aux 0 x ctx
    
(** Bidirectional Type Checking *)
type scene = {ctx : ctx; env : Sem.env; hi : Sem.lvl}
let nullscene = {ctx = []; env = []; hi = Lvl 0}
    
let assume (x : name) (typ : Sem.value) (scn : scene) : scene =
  { ctx = (x, typ) :: scn.ctx; env = (x, lazy (Sem.var scn.hi typ)) :: scn.env; hi = Sem.inc scn.hi }
    
let define (scp : scope) (x : name) (typ : Sem.value) (vl : Sem.value) (scn : scene) : scene =
  let extend = match scp with
  | Loc -> (x, lazy vl) :: scn.env
  | Top ->
    let unfd = lazy vl in
    let neut = lazy (Sem.Neut (Glue (scn.hi, unfd), [], typ)) in
    (x, neut) :: scn.env
  in { ctx = (x, typ) :: scn.ctx; env = extend; hi = Sem.inc scn.hi }

exception UnInferrable
exception TypeError of string
    
let rec infer (scn : scene) (expr : Sur.expr) : Syn.term * Sem.value =
  let names = List.map fst scn.ctx in
  match expr with
  | Ann (e, typ) ->
    let typ = check scn typ Sem.Uni in
    let typ = eval scn.env typ in
    let e   = check scn e typ in
    (e, typ)
  | Var x -> let (i, typ) = lookupVar x scn.ctx in (Var i, typ)
  | Lam (x, Some t, e) ->
    let t = check scn t Uni in
    let vt = eval scn.env t in
    let scn' = assume x vt scn in
    let (e, typ) = infer scn' e in
    let arrow = Syn.Pi ("", t, B (quote scn'.hi typ)) in
    (Lam (x, t, B e), eval scn.env arrow)
  | Pi (x, a, b) ->
    let a  = check scn a Sem.Uni in
    let va = eval scn.env a in
    let b  = check (assume x va scn) b Sem.Uni in
    (Pi (x, a, B b), Uni)
  | Sig fs ->
    let rec infer_fields (scn : scene) (fs : (name * Sur.expr) list) : (name * Syn.term) list =
      match fs with
      | [] -> []
      | (x, t) :: rest ->
        let t = check scn t Uni in
        let vt = eval scn.env t in
        let scn' = assume x vt scn in
        (x, t) :: infer_fields scn' rest
    in (Sig (infer_fields scn fs), Uni)
  | Rcd fs ->
    let rec infer_entries (scn : scene) (fs : (name * Sur.expr) list)
                          : (name * Syn.term) list * (name * Syn.term) list =
      match fs with
      | [] -> ([], [])
      | (x, e) :: rest ->
        let (e, vt) = infer scn e in
        let t = quote scn.hi vt in
        let ve = eval scn.env e in
        let scn' = define Loc x vt ve scn in
        let (rest, resttyp) = infer_entries scn' rest in
        ((x, e) :: rest, (x, t) :: resttyp)
    in let (fs, ts) = infer_entries scn fs in
    (Rcd fs, Sig (T {bdrs = ts; env = scn.env}))
  | Prod ts ->
    let ts = List.map (fun t -> check scn t Uni) ts in
    (Prod ts, Uni)
  | Tup es ->
    let es, ts = unzip @@ List.map (infer scn) es in
    (Tup es, Prod ts)
  | App (e1, e2) ->
    let (e1, t1) = infer scn e1 in begin
    match Sem.force_head t1 with
    | Pi (_, a, b) ->
      let e2 = check scn e2 a in
      let ve2 = eval scn.env e2 in
      let fam = inst b ve2 in
      (App (e1, e2), fam)
    | _ -> raise (TypeError ("can't apply on a non-function type " ^ pretty_term_under names e1))
    end
  | Proj (e, x) ->
    let (e, t) = infer scn e in
    begin match Sem.force_head t with
    | Sig fs ->
      let ve = eval scn.env e in
      let xt = field_type ve x fs in
      (Proj (e, x), xt)
    | _ -> raise (TypeError "can't project out of non-record type")
    end
  | ProjAt (e, i) ->
    let (e', t) = infer scn e in
    begin try
      begin match Sem.force_head t with
      | Sig (T {bdrs; _}) ->
        let x = List.nth (List.map fst bdrs) i in
        infer scn (Proj (e, x))
      | Prod ts ->
        (ProjAt (e', i), List.nth ts i)
      | _ -> raise (TypeError "can't project index out of non-product type")
      end
    with
    | Failure _ -> raise (TypeError ("can't project index " ^ string_of_int i ^ " out of smaller product"))
    end
  | Let (x, typ, e, rest) ->
    let (bdr, scn) = checkLet scn Loc x typ e in
    let (rest, resttyp) = infer scn rest in
    (bdr rest, resttyp)
  | Uni -> (Uni, Uni)
  | Bool -> (Bool, Uni)
  | True -> (True, Bool)
  | False -> (False, Bool)
  | BoolInd (Some mtv, scrut, tc, fc) ->
    let scrut = check scn scrut Bool in
    let vscrut = eval scn.env scrut in
    let mtv = check scn mtv bool_to_type in
    let vmtv = eval scn.env mtv in
    let typ = vApp vmtv vscrut in
    let tc = check scn tc (vApp vmtv True) in
    let fc = check scn fc (vApp vmtv False) in
    let ind = Syn.BoolInd {motive = mtv; tcase = tc; fcase = fc; scrut = scrut} in
    (ind, typ)
  | BoolInd (None, scrut, tc, fc) ->
    let scrut = check scn scrut Bool in
    let (tc, typ) = infer scn tc in
    let fc = check scn fc typ in
    let mtv = Syn.Lam ("_mtv", Bool, B (quote (Sem.inc scn.hi) typ)) in
    let ind = Syn.BoolInd {motive = mtv; tcase = tc; fcase = fc; scrut = scrut} in
    (ind, typ)
  | Nat -> (Nat, Uni)
  | NatZ -> (NatZ, Nat)
  | NatS n ->
    let n = check scn n Nat in
    (NatS n, Nat)
  | NatLit n ->
    let rec lit_to_nat (n : int) : Syn.term =
      if n < 0 then raise (TypeError "negative numbers not supported")
      else if n == 0 then NatZ
      else NatS (lit_to_nat (n - 1))
    in (lit_to_nat n, Nat)
  | NatInd (scrut, Some mtv, zc, (m, p, sc)) ->
    let scrut = check scn scrut Nat in
    let vscrut = eval scn.env scrut in
    let mtv = check scn mtv nat_to_type in
    let vmtv = eval scn.env mtv in
    let typ = vApp vmtv vscrut in
    let zc = check scn zc (vApp vmtv NatZ) in
    let sc = check scn (Lam (m, None, Lam (p, None, sc))) (nat_ind_step_type vmtv) in
    let ind = Syn.NatInd {motive = mtv; zcase = zc; scase = sc; scrut = scrut} in
    (ind, typ)
  | NatInd (_, None, _, _) -> raise (TypeError "unannotated nat induction unsupported")
  | _ -> print_endline ("\n\n" ^ pretty_expr expr); raise UnInferrable

and check (scn : scene) (expr : Sur.expr) (typ : Sem.value) : Syn.term =
  let names = List.map fst scn.ctx in
  match expr, Sem.force_head typ with
  | Lam (x, None, e), Pi (_, a, C {bdr = B bdr; env}) ->
    let fam = eval ((x, lazy (Sem.var scn.hi a)) :: env) bdr in
    let e = check (assume x a scn) e fam in
    Lam (x, quote scn.hi a, B e)
  | Tup es, Prod ts ->
    let es = List.map2 (check scn) es ts in
    Tup es
  | Rcd es, Sig fs ->
    let rec check_entries (scn : scene) (es : (name * Sur.expr) list) (T {bdrs; env} : Sem.tele) (acc : (name * Syn.term) list) =
      begin match es, bdrs with
      | [], [] -> List.rev acc
      | [], _ | _, [] -> raise (TypeError "record has less entries than its record type")
      | (x, e) :: es, (x', t) :: es' ->
        if x <> x' then raise (TypeError "nonmatching record labels") else
          let vt = eval env t in  
          let e = check scn e vt in
          let ve = eval scn.env e in
          let env' = (x, lazy ve) :: env in
          let scn' = define Loc x vt ve scn in
          check_entries scn' es (Sem.T {bdrs = es'; env = env'}) ((x, e) :: acc)
      end
    in Rcd (check_entries scn es fs [])
  | Tup es, Sig fs ->
    let lbls = tele_names fs in
    let es' = List.map2 (fun lbl e -> (lbl, e)) lbls es in
    check scn (Rcd es') (Sig fs)
  | Let (x, typ, e, rest), resttyp ->
    let (bdr, scn) = checkLet scn Loc x typ e in
    let rest = check scn rest resttyp in
    bdr rest
  | expr, expected ->
    let (texpr, actual) = infer scn expr in
    try
      conv scn.hi actual expected Uni;
      texpr
    with
      | UnEq s ->
        raise (TypeError (
        "inferred type " ^ pretty_term_under names (quote scn.hi actual)
        ^ " doesn't match expected type " ^ pretty_term_under names (quote scn.hi expected)
        ^ ", because: " ^ s))
      | IllTyped err -> raise (IllTyped (
        "while inferring " ^ pretty_expr expr ^ " inferred type " ^ pretty_term_under names (quote scn.hi actual)
      ^ " doesn't match expected type " ^ pretty_term_under names (quote scn.hi expected)
      ^ ", because: " ^ err))

and checkLet (scn : scene) (scp : scope) (x : name) (typ : Sur.expr option) (e : Sur.expr) : (Syn.term -> Syn.term) * scene =
  let (e, vtyp) = begin match typ with
  | Some typ ->
    let typ = check scn typ Uni in
    let vtyp = eval scn.env typ in
    let e = check scn e vtyp in
    (e, vtyp)
  | None ->
    try infer scn e
    with
    | UnInferrable -> raise (TypeError "uninferrable let-binding must be annotated")
  end in
  let ve = eval scn.env e in
  ((fun rest -> Let (scp, x, quote scn.hi vtyp, e, B rest)), define scp x vtyp ve scn)

(*
and commonType (scn : scene) (e1 : Sur.expr) (e2 : Sur.expr) (typ : Sem.value option) : Syn.term * Syn.term * Sem.value =
match typ with
| None ->
  begin try
    let (e1, typ) = infer scn e1 in
    let e2 = check scn e2 typ in
    (e1, e2, typ)
    with
    | UnInferrable ->
      let (e2, typ) = infer scn e2 in
      let e1 = check scn e1 typ in
      (e1, e2, typ)
    end
    | Some typ -> (check scn e1 typ, check scn e2 typ, typ)
*)