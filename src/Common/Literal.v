From Utils Require Import Int Tactics.

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

Lemma lit_eqb_refl : forall l, lit_eqb l l = true.
Proof.
  destruct l; simpl;
  auto using Z.eqb_refl, Bool.eqb_reflx.
Qed.