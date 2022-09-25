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
  | Sig fs -> Sig (T {bdrs = fs; env = env})
  | Rcd fs ->
    let rec process_fields (env : Sem.env) = function
      | [] -> []
      | (lbl, entry) :: rest ->
        let ventry = eval env entry in
        let env' = (lbl, lazy ventry) :: env in
        (lbl, ventry) :: process_fields env' rest
    in Rcd (process_fields env fs)
  | Prod ts -> Prod (List.map (eval env) ts)
  | Tup es -> Tup (List.map (eval env) es)
  | App (e1, e2) -> vApp (eval env e1) (eval env e2)
  | Proj (e, x) -> vProj x (eval env e)
  | ProjAt (e, i) -> vProjAt i (eval env e)
  | Let (scp, x, typ, body, B rest) ->
    begin match scp with
    | Top ->
      let typ' = eval env typ in
      let body' = lazy (eval env body) in
      let glue = Sem.Glue (Sem.height env, body') in
      let env' = (x, lazy (Sem.Neut (glue, [], typ'))) :: env in
      eval env' rest
    | Loc ->
      let body' = lazy (eval env body) in
      let env' = (x, body') :: env in
      eval env' rest
    end
  | Uni -> Uni
  | Bool -> Bool
  | True -> True
  | False -> False
  | BoolInd {motive = mtv; tcase = tc; fcase = fc; scrut = scrut} ->
    vBoolInd (eval env mtv) (eval env tc) (eval env fc) (eval env scrut)
  | Nat -> Nat
  | NatZ -> NatZ
  | NatS n -> NatS (eval env n)
  | NatInd {motive = mtv; zcase = zc; scase = sc; scrut} ->
    vNatInd (eval env mtv) (eval env zc) (eval env sc) (eval env scrut)
    
(** Instantiate a closure(/type family) at given type *)
and inst (C {bdr = B body; env = env} : Sem.closure) (base : Sem.value) : Sem.value =
  eval (("_x", lazy base) :: env) body
    
    
(** β-reduction helpers on values *)
and vApp (fnc : Sem.value) (arg : Sem.value) : Sem.value =
  match Sem.force_head fnc with
  | Neut (hd, sp, typ) ->
    begin match Sem.force_head typ with
    | Pi (_, base, fam) ->
      let hd' = Sem.head_map (fun vl -> vApp vl arg) hd in
      let sp' = (Sem.App {arg = arg; base = base}) :: sp in
      Neut (hd', sp', inst fam base)
    | _ -> raise (IllTyped "can't apply on a non-pi neutral")
    end
  | Lam (_, _, body) -> inst body arg
  | _ -> raise (IllTyped "can't apply on non-lambda")
and vProj (x : name) (vl : Sem.value) : Sem.value =
  match Sem.force_head vl with
  | Rcd fs ->
    begin match List.assoc_opt x fs with
    | None ->
      let lbls = List.map fst fs in
      let set = "{" ^ String.concat ", " lbls ^ "}" in
      raise (IllTyped ("can't project out of record " ^ set ^ " without given label " ^ x))
    | Some e -> e
    end
  | Neut (hd, sp, typ) ->
    begin match Sem.force_head typ with
    | Sig fs ->
      let hd' = Sem.head_map (vProj x) hd in
      let sp' = Sem.Proj x :: sp in
      let typ = field_type vl x fs in
      Neut (hd', sp', typ)
    | _ -> raise (IllTyped "can't project field from a non-record neutral")
    end
  | _ -> raise (IllTyped "can't project field from non-record")
and vProjAt (i : int) (vl : Sem.value) : Sem.value =
  match Sem.force_head vl with
  | Tup es ->
    begin try List.nth es i with
    | Failure _ -> raise (IllTyped "index outside of tuple")
    end
  | Rcd fs ->
    let entries = List.map snd fs in
    begin try List.nth entries i with
    | Failure _ -> raise (IllTyped "index outside of record")
    end
  | Neut (hd, sp, typ) ->
    begin match Sem.force_head typ with
    | Prod ts ->
      let typ = begin try List.nth ts i with
      | Failure _ -> raise (IllTyped "index outside of product")
      end in
      let hd' = Sem.head_map (vProjAt i) hd in
      let sp' = Sem.ProjAt i :: sp in
      Neut (hd', sp', typ)
    | Sig (T {bdrs; _} as fs) ->
      let typ = begin match List.nth_opt bdrs i with
      | None -> raise (IllTyped "")
      | Some (lbl, _) -> field_type vl lbl fs
      end in
      let hd' = Sem.head_map (vProjAt i) hd in
      let sp' = Sem.ProjAt i :: sp in
      Neut (hd', sp', typ)
    | Neut (Var (Lvl typlvl), _typsp, Uni) -> failwith ("oops " ^ string_of_int typlvl)
    | _ -> raise (IllTyped "can't project index from non-product neutral")
    end    
  | _ -> raise (IllTyped "can't project index from non-tuple")
and vBoolInd (mtv : Sem.value) (tc : Sem.value) (fc : Sem.value) (scrut : Sem.value) : Sem.value =
  match scrut with
  | True -> tc
  | False -> fc
  | Neut (hd, sp, typ) ->
    begin match Sem.force_head typ with
    | Bool ->
      let em = Sem.BoolInd {motive = mtv; tcase = tc; fcase = fc} in
      let typ = vApp mtv scrut in
      Neut (hd, em :: sp, typ)
    | _ -> raise (IllTyped "can't eliminate value not of type Bool")
    end
  | _ -> raise (IllTyped "can't eliminate a non-boolean")
and vNatInd (mtv : Sem.value) (zc : Sem.value) (sc : Sem.value) (scrut : Sem.value) : Sem.value =
  match scrut with
  | NatZ -> zc
  | NatS n -> vApp (vApp sc n) (vNatInd mtv zc sc n)
  | Neut (hd, sp, typ) ->
    begin match Sem.force_head typ with
    | Nat ->
      let em = Sem.NatInd {motive = mtv; zcase = zc; scase = sc} in
      let typ = vApp mtv scrut in
      Neut (hd, em :: sp, typ)
    | _ -> raise (IllTyped "can't eliminate value not of type Nat")
    end
  | _ -> raise (IllTyped "can't eliminate a non-natural")

and field_type (vl : Sem.value) (x : name) (T {bdrs; env} : Sem.tele) : Sem.value =
  (* TODO improve to linear time! ? *)
  match bdrs with
  | [] -> raise (IllTyped "label doesn't appear in record type")
  | (lbl, t) :: rest ->
    if x = lbl
      then eval env t
      else
        let entry = lazy (vProj lbl vl) in
        let env' = (x, entry) :: env in
        field_type vl x (T {bdrs = rest; env = env'})

let inst_tele_at (vl : Sem.value) (tel : Sem.tele) : (name * Sem.value * Sem.tele) option =
  let T {bdrs; env} = tel in
  match bdrs with
  | [] -> None
  | (x, t) :: rest ->
    let vt = eval env t in
    let env' = (x, lazy vl) :: env in
    Some (x, vt, T {bdrs = rest; env = env'})

let inst_tele (siz : Sem.lvl) (tel : Sem.tele) : (name * Sem.value * Sem.tele) option =
  let T {bdrs; env} = tel in
  match bdrs with
  | [] -> None
  | (x, t) :: rest ->
    let vt = eval env t in
    let env' = (x, lazy (Sem.var siz vt)) :: env in
    Some (x, vt, T {bdrs = rest; env = env'})

let tele_names (T {bdrs; _} : Sem.tele) : name list = List.map fst bdrs

let lvl2idx (Lvl siz : Sem.lvl) (Lvl i : Sem.lvl) = Syn.Idx (siz - i - 1)

let rec quote (siz : Sem.lvl) (vl : Sem.value) : Syn.term =
  match vl with
  | Pi (x, a, b) ->
    let fam = inst b (Sem.var siz a) in
    Pi (x, quote siz a, B (quote (Sem.inc siz) fam))
  | Lam (x, t, e) ->
    let fam = inst e (Sem.var siz t) in
    Lam (x, quote siz t, B (quote (Sem.inc siz) fam))
  | Sig fs -> Sig (quote_tele siz fs)
  | Rcd fs -> Rcd (quote_rcd siz fs)
  | Prod ts -> Prod (List.map (quote siz) ts)
  | Tup es -> Tup (List.map (quote siz) es)
  | Uni -> Uni
  | Bool -> Bool
  | True -> True
  | False -> False
  | Nat -> Nat
  | NatZ -> NatZ
  | NatS n -> NatS (quote siz n)
  | Neut (hd, sp, _) -> quote_neut siz hd sp

and quote_tele (siz : Sem.lvl) (tel : Sem.tele) : (name * Syn.term) list =
  match inst_tele siz tel with
  | None -> []
  | Some (x, t, rest) -> (x, quote siz t) :: quote_tele (Sem.inc siz) rest
and quote_rcd (siz : Sem.lvl) (fs : (name * Sem.value) list) : (name * Syn.term) list =
  match fs with
  | [] -> []
  | (x, e) :: rest -> (x, quote siz e) :: quote_rcd (Sem.inc siz) rest

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
    BoolInd {motive = quote siz motive; tcase = quote siz tcase; fcase = quote siz fcase; scrut = scrut}
  | NatInd {motive; zcase; scase} ->
    NatInd {motive = quote siz motive; zcase = quote siz zcase; scase = quote siz scase; scrut = scrut}

and quote_head (siz : Sem.lvl) (hd : Sem.head) : Syn.term =
  match hd with
  | Var i | Glue (i, _) ->
    let (Idx i) as idx = lvl2idx siz i in
    if i < 0 then failwith "quoting negative index"
    else Var idx

(* useful constants *)
let bool_to_type = (* Bool → Type *)
  Sem.Pi ("", Bool, C {bdr = B Uni; env = []})
let nat_to_type = (* Nat → Type *)
  Sem.Pi ("", Nat, C {bdr = B Uni; env = []})
let nat_ind_step_type (mtv : Sem.value) = (* (n : Nat) → mtv n → mtv (Succ n) *)
  Sem.Pi ("n", Nat, C {bdr = B (Syn.Pi ("",
  quote (Lvl 1) (vApp mtv (Sem.var (Lvl 0) Nat)),
  B (quote (Lvl 2) (vApp mtv (NatS (Sem.var (Lvl 0) Nat)))))); env = []})