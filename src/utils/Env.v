Require Export PeanoNat List.
Require Import Lia.
From Utils Require Import Tactics.

Open Scope nat_scope.
Open Scope list_scope.

Definition env (A: Type) : Type := list (nat * A).

Definition empty {A: Type} : env A := nil.
Fixpoint lookup {A: Type} (e : env A) (n: nat) : option A :=
  match e with 
  | nil => None 
  | h :: t => 
    if ((fst h) =? n) then Some (snd h)
    else lookup t n
  end.
Definition add {A: Type} (e : env A) (n: nat) (a: A) : env A := 
  (n, a) :: e.

Theorem lookup_empty: forall A k, lookup (@empty A) k = None.
Proof.
  auto.
Qed.

Theorem lookup_add_eq: forall A (e : env A) n1 n2 v,
  n1 = n2 -> 
    lookup (add e n1 v) n2 = Some v.
Proof.
  intros; simpl; subst.
  rewrite Nat.eqb_refl.
  auto.
Qed.

Theorem lookup_add_ne: forall A (e : env A) n1 n2 v,
  n1 <> n2 ->
    lookup (add e n1 v) n2 = lookup e n2.
Proof.
  intros; simpl.
  apply_anywhere Nat.eqb_neq.
  rewrite H.
  auto.
Qed.

Opaque env empty lookup add.
