open Common
module Syn = Syntax

type lvl = Lvl of int
(** Values use levels (counting the environment from the left) which gives us weakening for free. *)

(** We separate out of values a distinct subdomain [neut] for neutral values,
    those which get "stuck" on variables. Intuitively, when the variables would
    be expanded in the future, we'd be able to perform more β-reductions on neutral
    terms. Non-neutral values are already fully β-reduced. *)
type value =
  | Pi of name * value * closure
  | Lam of name * value * closure
  | Sig of tele
  | Rcd of (name * value) list
  | Prod of value list
  | Tup of value list
  | Uni
  | Bool
  | True
  | False
  | Nat
  | NatZ
  | NatS of value
  | Neut of head * spine * value

and head =
  | Var of lvl
  | Glue of lvl * value Lazy.t (** Glued Evaluation
      Allows us to unfold top-level definitions lazily, leads to reduced term sizes.
      [Glue] stores along with the [neut] itself another lazy version of the same
      value in which all top level definitions are unfolded. *)
and elim =
  | Proj of name
  | ProjAt of int
  | App of {arg : value; base : value}
    (** [base] is the type of [arg] (base of the pi's type-family),
        used later in the type-directed conversion. *)
  | BoolInd of {motive : value; tcase : value; fcase : value}
  | NatInd of {motive : value; zcase : value; scase : value}
and spine = elim list
(** We use a spine based representation of neutral terms where the head is the variable
    it got stuck on, and it can be easily accessed in constant time. Example in pseudo-notation:
    A spine [[App "y", Fst, IfThenElse 1 -1, Snd]] with head [Var "x"] represents the expression
    `snd (if (fst (x y)) then 1 else -1)` *)

and closure =
  | C of {bdr : Syn.term binder; env : env}
and tele =
  | T of {bdrs : (name * Syn.term) list; env : env}
and env = (name * value Lazy.t) list
(*
| Emp
| Local of env * name * value
| Toplevel of env * name * value (*TODO need Lazy.t here?*)
*)

exception OutOfBounds of string
let rec atIdx (env : env) (Idx i : Syn.idx) : value =
  match env with
  | [] -> raise (OutOfBounds ("idx" ^ string_of_int i))
  | (_, v) :: env' ->
    if i == 0
      then Lazy.force v
      else atIdx env' (Idx (i - 1))
let height (env : env) : lvl = (* TODO still need this? ideally just use scn.hi always *)
  let rec aux (env : env) : int =
    match env with
    | [] -> 0
    | _ :: env' -> 1 + aux env'
  in Lvl (aux env)
let rec names (env : env) : name list = (* TODO still need this? ideally store names separately in scene *)
  match env with
  | [] -> []
  | (x, _) :: env' -> x :: names env'

(** We use this helper function to propagate projections (lazily!) through
    [Glue] into the unfolded version of the value. *)
let head_map (f : value -> value) (hd : head) : head =
  match hd with
  | Var _ -> hd
  | Glue (i, unfd) -> Glue (i, Lazy.map f unfd)

let inc (Lvl l : lvl) : lvl = Lvl (l + 1)
let nextvar (siz : lvl) (typ : value) : value = Neut (Var siz, [], typ)
let var (i : lvl) (typ : value) : value = Neut (Var i, [], typ)

let rec force_head (vl : value) : value =
  match vl with
  | Neut (Glue (_, unfd), _, _) -> force_head (Lazy.force unfd)
  | _ -> vl