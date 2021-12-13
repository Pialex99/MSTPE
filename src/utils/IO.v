From Utils Require Import Int.

Open Scope list_scope.

Record IO := mk_io {input : list int; output : list int}.

Definition outputs io o := mk_io (input io) (o::output io).

Definition get_input io := 
  match input io with
  | nil => None 
  | i :: input => Some (i, mk_io input (output io))
  end.