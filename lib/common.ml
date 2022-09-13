type name = string
type scope = Loc | Top

type 'a binder = B of 'a
(** [binder] is a wrapper to remind us when a term depends on a new bound var. *)

let rec unzip (ps : ('a * 'b) list) : 'a list * 'b list =
  match ps with
  | [] -> ([], [])
  | (x, y) :: rest ->
    let (xs, ys) = unzip rest in
    (x :: xs, y :: ys)