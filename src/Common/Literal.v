From Utils Require Import Int.

Inductive literal : Set := 
| IntLit (n: int) 
| BoolLit (b: bool)
| UnitLit.

Definition lit_eqb l1 l2 :=
  match l1, l2 with
  | IntLit n1, IntLit n2 => BinIntDef.Z.eqb n1 n2
  | BoolLit b1, BoolLit b2 => Bool.eqb b1 b2
  | UnitLit, UnitLit => true
  | _, _ => false
  end.