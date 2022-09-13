open Common
module PP = Pretty

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
  | Lam (x, typ, bound) -> Lam (x, eval env typ, C {bdr = bound; env = env})
  | Rcd fs -> Rcd (T {bdrs = fs; env = env})
  | Dict fs ->
    let rec process_fields (env : Sem.env) = function
      | [] -> []
      | (lbl, entry) :: rest ->
        let ventry = eval env entry in
        let env' = Sem.Toplevel (env, lbl, ventry) in
        (lbl, ventry) :: process_fields env' rest
    in Dict (process_fields env fs)
  | Prod ts -> Prod (List.map (eval env) ts)
  | Tup es -> Tup (List.map (eval env) es)
  | App (e1, e2) -> vApp (eval env e1) (eval env e2)
  | Proj (e, x) -> vProj x (eval env e)
  | ProjAt (e, i) -> vProjAt i (eval env e)
  | Let (_, x, _, body, B rest) ->
    (*begin match scp with
    | Top ->
      let typ' = eval env typ in
      let body' = lazy (eval env body) in
      let glue = Sem.Glue (Sem.height env, body') in
      let env' = Sem.Toplevel (env, x, Neut (glue, [], typ')) in
      eval env' rest
    | Loc ->
    end
      *)
      let body' = eval env body in
      let env' = Sem.Local (env, x, body') in
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
    
    
(** β-reduction helpers *)
and vApp (fnc : Sem.value) (arg : Sem.value) : Sem.value =
  match fnc with
  | Lam (_, _, body) -> inst body arg
  | Neut (hd, sp, Pi (_, base, fam)) ->
    let hd' = Sem.head_map (fun vl -> vApp vl arg) hd in
    let sp' = (Sem.App {arg = arg; base = base}) :: sp in
    Neut (hd', sp', inst fam base)
  | _ -> raise (IllTyped "can't apply on non-lambda")
and vProj (x : name) (vl : Sem.value) : Sem.value =
  match vl with
  | Dict fs ->
    begin match List.assoc_opt x fs with
    | None ->
      let lbls = List.map fst fs in
      let set = "{" ^ String.concat ", " lbls ^ "}" in
      raise (IllTyped ("can't project out of dictionary " ^ set ^ " without given label " ^ x))
    | Some e -> e
    end
  | Neut (hd, sp, Rcd fs) ->
    let hd' = Sem.head_map (vProj x) hd in
    let sp' = Sem.Proj x :: sp in
    let typ = field_type vl x fs in
    Neut (hd', sp', typ)
  | _ -> raise (IllTyped "can't project field from non-record")
and vProjAt (i : int) (vl : Sem.value) : Sem.value =
  match vl with
  | Tup es ->
    begin try List.nth es i with
    | Failure _ -> raise (IllTyped "index outside of tuple")
    end
  | Dict fs ->
    let entries = List.map snd fs in
    begin try List.nth entries i with
    | Failure _ -> raise (IllTyped "index outside of dictionary")
    end
  | Neut (hd, sp, Prod ts) ->
    let typ = begin try List.nth ts i with
    | Failure _ -> raise (IllTyped "index outside of product")
    end in
    let hd' = Sem.head_map (vProjAt i) hd in
    let sp' = Sem.ProjAt i :: sp in
    Neut (hd', sp', typ)
  | Neut (hd, sp, Rcd (T {bdrs; _} as fs)) ->
    let typ = begin match List.nth_opt bdrs i with
    | None -> raise (IllTyped "")
    | Some (lbl, _) -> field_type vl lbl fs
    end in
    let hd' = Sem.head_map (vProjAt i) hd in
    let sp' = Sem.ProjAt i :: sp in
    Neut (hd', sp', typ)
  | _ -> raise (IllTyped "can't project index from non-tuple")

and field_type (vl : Sem.value) (x : name) (T {bdrs; env} : Sem.tele) : Sem.value =
  (* TODO improve to linear time! ? *)
  match bdrs with
  | [] -> raise (IllTyped "label doesn't appear in record type")
  | (lbl, t) :: rest ->
    if x = lbl
      then eval env t
      else
        let entry = vProj lbl vl in
        let env' = Sem.Toplevel (env, x, entry) in
        field_type vl x (T {bdrs = rest; env = env'})

let inst_tele_at (vl : Sem.value) (tel : Sem.tele) : (name * Sem.value * Sem.tele) option =
  let T {bdrs; env} = tel in
  match bdrs with
  | [] -> None (*raise (Invalid_argument "can't step empty telescope")*)
  | (x, t) :: rest ->
    let vt = eval env t in
    (*let t' = quote siz vt in*)
    let env' = Sem.Toplevel (env, x, vl) in
    Some (x, vt, T {bdrs = rest; env = env'})

let inst_tele (siz : Sem.lvl) (tel : Sem.tele) : (name * Sem.value * Sem.tele) option =
  let T {bdrs; env} = tel in
  match bdrs with
  | [] -> None (*raise (Invalid_argument "can't step empty telescope")*)
  | (x, t) :: rest ->
    let vt = eval env t in
    (*let t' = quote siz vt in*)
    let env' = Sem.Toplevel (env, x, Sem.var siz vt) in
    Some (x, vt, T {bdrs = rest; env = env'})

let lvl2idx (Lvl siz : Sem.lvl) (Lvl i : Sem.lvl) = Syn.Idx (siz - i - 1)

let rec quote (siz : Sem.lvl) (vl : Sem.value) : Syn.term =
  match vl with
  | Pi (x, a, b) ->
    let fam = inst b (Sem.var siz a) in
    Pi (x, quote siz a, B (quote (Sem.inc siz) fam))
  | Lam (x, t, e) ->
    let fam = inst e (Sem.var siz t) in
    Lam (x, quote siz t, B (quote (Sem.inc siz) fam))
  | Rcd fs -> Rcd (quote_tele siz fs)
  | Dict fs -> Dict (quote_dict siz fs)
  | Prod ts -> Prod (List.map (quote siz) ts)
  | Tup es -> Tup (List.map (quote siz) es)
  | Uni -> Uni
  | Bool -> Bool
  | True -> True
  | False -> False
  | Neut (hd, sp, _) -> quote_neut siz hd sp

and quote_tele (siz : Sem.lvl) (tel : Sem.tele) : (name * Syn.term) list =
  match inst_tele siz tel with
  | None -> []
  | Some (x, t, rest) -> (x, quote siz t) :: quote_tele (Sem.inc siz) rest
and quote_dict (siz : Sem.lvl) (fs : (name * Sem.value) list) : (name * Syn.term) list =
  match fs with
  | [] -> []
  | (x, e) :: rest -> (x, quote siz e) :: quote_dict (Sem.inc siz) rest

and quote_neut (siz : Sem.lvl) (hd : Sem.head) (sp : Sem.spine) : Syn.term =
  List.fold_right (quote_elim siz) sp (quote_head siz hd)

and quote_elim (siz : Sem.lvl) (em : Sem.elim) (scrut : Syn.term) : Syn.term =
  match em with
  | Proj x -> Proj (scrut, x)
  | ProjAt i -> ProjAt (scrut, i)
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