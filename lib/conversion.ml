module Sem = Semantics
open Eval
open Pretty

(** Conversion Checking
    This function takes two values of the same type and tells us
    whether they're indeed equal up to β and η conversions. *)
exception UnEq of string
let rec conv (siz : Sem.lvl) (e1 : Sem.value) (e2 : Sem.value) (typ : Sem.value) : unit =
  match e1, e2, typ with
  | Pi (_, base1, fam1), Pi (_, base2, fam2), Uni
  | Sig (_, base1, fam1), Sig (_, base2, fam2), Uni ->
    conv siz base1 base2 Uni;
    let body1 = instvar fam1 base1 in
    let body2 = instvar fam2 base2 in
    conv (Sem.inc siz) body1 body2 Uni
  | Pi  _, Pi  _, _
  | Sig _, Sig _, _ -> raise (IllTyped "can't convert formers under wrong type")
  | Pi  _, _    , _
  | Sig _, _    , _
  | _    , Pi  _, _
  | _    , Sig _, _ -> raise (UnEq "type former mismtach")

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
  
  | e1, e2, Sig (_, base, fam) ->
    let fst1 = vFst e1 in
    let fst2 = vFst e2 in
    conv siz fst1 fst2 base;
    let typ = inst fam fst1 in
    conv siz (vSnd e1) (vSnd e2) typ
  | Pair _, _, _
  | _, Pair _, _ -> raise (UnEq "doesn't match pair")

  | Neut (hd1, sp1, typ1), Neut (hd2, sp2, typ2), _ ->
    conv     siz typ1 typ2 Uni;
    neutconv siz hd1 sp1 hd2 sp2 typ1
    
and neutconv (siz : Sem.lvl) (hd1 : Sem.head) (sp1 : Sem.spine)
                             (hd2 : Sem.head) (sp2 : Sem.spine) (typ : Sem.value) : unit =
  match hd1, hd2 with
  | Var x1, Var x2 ->
    if x1 = x2
      then spineconv siz sp1 sp2
      else raise (UnEq "var heads don't match")
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
  | Fst, Fst | Snd, Snd -> ()
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