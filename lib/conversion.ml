module Sem = Semantics
open Eval
open Pretty

(** Conversion Checking
    This function takes two values of the same type and tells us
    whether they're indeed equal up to β and η conversions. *)
exception UnEq of string
let rec conv (siz : Sem.lvl) (e1 : Sem.value) (e2 : Sem.value) (typ : Sem.value) : unit =
  match e1, e2, typ with
  | Pi (_, base1, fam1), Pi (_, base2, fam2), Uni ->
    conv siz base1 base2 Uni;
    let var = Sem.nextvar siz base1 in
    let body1 = inst fam1 var in
    let body2 = inst fam2 var in
    conv (Sem.inc siz) body1 body2 Uni
  (*| Sig (_, base1, fam1), Sig (_, base2, fam2), Uni -> _*)
  (*| Sig _, Sig _, _*) 
  | Pi  _, Pi  _, _ -> raise (IllTyped "can't convert pi's under wrong type")
  | Pi  _, _    , _
  (*| Sig _, _    , _*)
  | _    , Pi  _, _
  (*| _    , Sig _, _*) -> raise (UnEq "type former mismtach")

  | Prod _, Rcd _, Uni
  | Rcd _, Prod _, Uni -> failwith "TODO18"
  | Prod _, Rcd _, _
  | Rcd _, Prod _, _ -> raise (UnEq "can't convert record and product under wrong type")

  | Rcd fs1, Rcd fs2, Uni -> teleconv siz fs1 fs2
  | Rcd _, Rcd _, _ -> raise (UnEq "can't convert record types under wrong type")
  | Rcd _, _, _
  | _, Rcd _, _ -> raise (UnEq "can't convert record with non-record")

  | Prod ts1, Prod ts2, Uni ->
    ignore @@ List.map2 (fun v1 v2 -> conv siz v1 v2 Uni) ts1 ts2
  | Prod _, Prod _, _ -> raise (UnEq "can't convert products under wrong type")
  | Prod _, _, _
  | _, Prod _, _ -> raise (UnEq "doesn't match product type")


  | Uni, Uni, Uni -> ()
  | Uni, Uni, _   -> raise (IllTyped "can't convert Type's under wrong type")
  | Uni, _  , _
  | _  , Uni, _   -> raise (UnEq "doesn't match Type")

  | Bool, Bool, Uni -> ()
  | Bool, Bool, _   -> raise (IllTyped "can't convert Bool's under wrong type")
  | Bool, _   , _
  | _   , Bool, _   -> raise (UnEq "doesn't match Bool")

  | True , True , Bool
  | False, False, Bool -> ()
  | True , True , _
  | False, False, _    -> raise (IllTyped "can't convert bool terms under wrong type")
  | True , _    , _
  | False, _    , _
  | _    , True , _
  | _    , False, _    -> raise (UnEq "doesn't match boolean value")

  | e1, e2, Pi (_, base, fam) ->
    let var = Sem.nextvar siz base in
    let res1 = vApp e1 var in
    let res2 = vApp e2 var in
    let body = inst fam var in
    conv (Sem.inc siz) res1 res2 body
  | Lam _, _, _
  | _, Lam _, _ -> raise (UnEq "doesn't match lambda")
  
  (*
  | e1, e2, Sig (_, base, fam) ->
    let fst1 = vFst e1 in
    let fst2 = vFst e2 in
    conv siz fst1 fst2 base;
    let typ = inst fam fst1 in
    conv siz (vSnd e1) (vSnd e2) typ
  | Pair _, _, _
  | _, Pair _, _ -> raise (UnEq "doesn't match pair")
  *)

  | _e1, _e2, Rcd _fs -> failwith "TODO7"
  | Dict _, _, _
  | _, Dict _, _ -> failwith "TODO8"

  | _e1, _e2, Prod _fs -> failwith "TODO9"
  | Tup _, _, _
  | _, Tup _, _ -> failwith "TODO10"

  | Neut (hd1, sp1, typ1), Neut (hd2, sp2, typ2), _ ->
    conv     siz typ1 typ2 Uni;
    neutconv siz hd1 sp1 hd2 sp2 typ1
    
and neutconv (siz : Sem.lvl) (hd1 : Sem.head) (sp1 : Sem.spine)
                             (hd2 : Sem.head) (sp2 : Sem.spine) (typ : Sem.value) : unit =
  match hd1, hd2 with
  | Var (Lvl x1), Var (Lvl x2) ->
    if x1 = x2
      then spineconv siz sp1 sp2
      else raise (UnEq ("var heads don't match (" ^ string_of_int x1 ^ "≠" ^ string_of_int x2 ^")"))
  | Glue (x1, unfd1), Glue (x2, unfd2) ->
    if x1 = x2
    then spineconv siz sp1 sp2
    else
      let v1' = Lazy.force unfd1 in
      let v2' = Lazy.force unfd2 in
      conv siz v1' v2' typ
  | Var _, Glue _ | Glue _, Var _ -> raise (UnEq "idk how to compare var to glue") (* TODO could try unfolding anyway? *)
    
and spineconv (siz : Sem.lvl) (sp1 : Sem.spine) (sp2 : Sem.spine) : unit =
  match sp1, sp2 with
  | [], [] -> ()
  | em1 :: rest1, em2 :: rest2 ->
    elimconv siz em1 em2;
    spineconv siz rest1 rest2;
  | _ -> raise (UnEq "spines have different lengths")
and elimconv (siz : Sem.lvl) (em1 : Sem.elim) (em2 : Sem.elim) : unit =
  match em1, em2 with
  (*| Fst, Fst | Snd, Snd -> ()*)
  | Proj _x1, Proj _x2 -> failwith "TODO11"
  | ProjAt _i1, ProjAt _i2 -> failwith "TODO12"
  | App {arg = arg1; base = base1}, App {arg = arg2; base = base2} ->
    conv siz base1 base2 Uni;
    conv siz arg1 arg2 base1
  | BoolInd {motive = mtv1; tcase = _; fcase = _},
    BoolInd {motive = mtv2; tcase = _; fcase = _} ->
    let famtyp = Sem.Pi ("dum", Bool, C {bdr = B Uni; env = Emp}) (* Bool → Type *) in
    conv siz mtv1 mtv2 famtyp;
    failwith "unfinished BoolInd conversion"
    (*TODO finish this!!! check cases...!*)
  | _ -> raise (UnEq "eliminators don't match")

and teleconv (siz : Sem.lvl) (tel1 : Sem.tele) (tel2 : Sem.tele) : unit =
  match inst_tele siz tel1, inst_tele siz tel2 with
  | None, None -> ()
  | None, Some _ | Some _, None -> raise (UnEq "can't convert telescopes of different lengths")
  | Some (x1, t1, rest1), Some (x2, t2, rest2) ->
    if x1 <> x2 then raise (UnEq "labels don't match at heads of telescopes")
    else
      conv siz t1 t2 Uni;
      teleconv (Sem.inc siz) rest1 rest2