type name = string
type scope = Loc | Top

type 'a binder = B of 'a
(** [binder] is a wrapper to remind us when a term depends on a new bound var. *)