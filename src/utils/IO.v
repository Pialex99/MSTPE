From Utils Require Import Int.

Record IO := {input : list int; output : list int}.

Definition outputs io o := 
  {|input:= input io; output:= o::output io|}.
