module Sem = Semantics
open Eval
open Pretty

(** Conversion Checking
    This function takes two values of the same type and tells us
    whether they're indeed equal up to β and η conversions. *)
exception UnEq of string
exception FormerMismatch of Sem.value * Sem.value * Sem.value

let rec conv (siz : Sem.lvl) (e1 : Sem.value) (e2 : Sem.value) (typ : Sem.value) : unit =
  let e1 = Sem.force_head e1 in
  let e2 = Sem.force_head e2 in
  let typ = Sem.force_head typ in
  match e1, e2, typ with
  | Pi (_, base1, fam1), Pi (_, base2, fam2), Uni ->
    conv siz base1 base2 Uni;
    let var = Sem.nextvar siz base1 in
    let body1 = inst fam1 var in
    let body2 = inst fam2 var in
    conv (Sem.inc siz) body1 body2 Uni
  | Pi  _, Pi  _, _ -> raise (IllTyped "can't convert pi's under wrong type")
  | Pi  _, _    , _
  | _    , Pi  _, _ -> raise (UnEq "type former mismatch")

  | Prod ts, Sig fs, Uni
  | Sig fs, Prod ts, Uni ->
    let rec conv_fields (siz : Sem.lvl) (fs : Sem.tele) (ts : Sem.value list) =
      begin match Eval.inst_tele siz fs, ts with
      | Some (_, typ, tel), t :: rest ->
        conv siz typ t Uni;
        conv_fields (Sem.inc siz) tel rest
      | None, [] -> ()
      | _ -> raise (UnEq "can't convert record and product of different lengths")
      end
    in conv_fields siz fs ts
  (* failwith "TODO: should this be convertible?" *)
  | Prod _, Sig _, _
  | Sig _, Prod _, _ -> raise (UnEq "can't convert record and product under wrong type")

  | Sig fs1, Sig fs2, Uni -> teleconv siz fs1 fs2
  | Sig _, Sig _, _ -> raise (UnEq "can't convert record types under wrong type")
  | Sig _, _, _
  | _, Sig _, _ -> raise (UnEq "can't convert record with non-record")

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

  | Nat, Nat, Uni -> ()
  | Nat, Nat, _ -> raise (IllTyped "can't convert Nat's under wrong type")
  | Nat, _  , _
  | _  , Nat, _ -> raise (UnEq "doesn't match Nat")

  | NatZ, NatZ, Nat -> ()
  | NatS n1, NatS n2, Nat -> conv siz n1 n2 Nat
  | NatZ, NatZ, _
  | NatS _, NatS _, _ -> raise (IllTyped "can't convert Nat terms under wrong type")
  | NatZ, _, _
  | _, NatZ, _
  | NatS _, _, _
  | _, NatS _, _ -> raise (UnEq "doesn't match natural number value")

  | e1, e2, Pi (_, base, fam) ->
    let var = Sem.nextvar siz base in
    let res1 = vApp e1 var in
    let res2 = vApp e2 var in
    let body = inst fam var in
    conv (Sem.inc siz) res1 res2 body
  | Lam _, _, _
  | _, Lam _, _ -> raise (IllTyped "converting lambda under wrong type")

  | e1, e2, Sig fs ->
    let rec conv_fields (siz : Sem.lvl) (fs : Sem.tele) : unit =
      match inst_tele siz fs with
      | None -> ()
      | Some (lbl, typ, rest) ->
        conv siz (vProj lbl e1) (vProj lbl e2) typ;
        conv_fields (Sem.inc siz) rest
    in conv_fields siz fs
  | Rcd _, _, _
  | _, Rcd _, _ -> raise (IllTyped "converting records under wrong type")

  | e1, e2, Prod ts ->
    List.iteri (fun i t -> conv siz (vProjAt i e1) (vProjAt i e2) t) ts;
  | Tup _, _, _
  | _, Tup _, _ -> raise (IllTyped "converting tuple under wrong type")

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
    spineconv siz rest1 rest2;
    elimconv siz em1 em2;
  | _ -> raise (UnEq "spines have different lengths")
and elimconv (siz : Sem.lvl) (em1 : Sem.elim) (em2 : Sem.elim) : unit =
  match em1, em2 with
  | Proj x1, Proj x2 -> if x1 = x2 then () else raise (UnEq "projecting different labels")
  | ProjAt i1, ProjAt i2 -> if i1 = i2 then () else raise (UnEq "projecting different indices")
  | App {arg = arg1; base = base1}, App {arg = arg2; base = base2} ->
    conv siz base1 base2 Uni;
    conv siz arg1 arg2 base1
  | BoolInd {motive = mtv1; tcase = tc1; fcase = fc1},
    BoolInd {motive = mtv2; tcase = tc2; fcase = fc2} ->
    let famtyp = bool_to_type in
    conv siz mtv1 mtv2 famtyp;
    conv siz tc1 tc2 (vApp mtv1 True);
    conv siz fc1 fc2 (vApp mtv1 False)
  | NatInd {motive = mtv1; zcase = zc1; scase = sc1},
    NatInd {motive = mtv2; zcase = zc2; scase = sc2} ->
    let famtyp = nat_to_type in
    conv siz mtv1 mtv2 famtyp;
    conv siz zc1 zc2 (vApp mtv1 NatZ);
    let succtyp = nat_ind_step_type mtv1 in
    conv siz sc1 sc2 (vApp mtv1 succtyp)
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