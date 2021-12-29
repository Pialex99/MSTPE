Require Export Lia String.

#[global]
Hint Extern 50 => lia: lia.
#[global]
Hint Extern 50 => exfalso: exfalso.

Ltac subst_all := 
  repeat lazymatch goal with 
  | s := _ |- _ =>
    subst s
  end.

Ltac destruct_exist_H :=
  match goal with 
  | H: exists _, _ |- _ => 
      destruct H
  end.

Ltac destruct_or_H := 
  match goal with 
  | H: _ \/ _ |- _ => 
    destruct H
  end.

Ltac destruct_and_H :=
  match goal with 
  | H: _ /\ _ |- _ => 
    destruct H
  end.

Ltac invert H := inversion H; subst; clear H.

Ltac rewrite_S n :=
  let a := fresh "A" in
  assert (a: S n = n + 1) by lia;
  rewrite a in *; clear a.

Lemma max_le : forall n m k, 
  n <= k /\ m <= k -> Nat.max n m <= k.
Proof. 
  lia.
Qed.

Global Opaque Nat.max.

Ltac simpl_lia :=
  match goal with 
  | |- Nat.max ?n ?m <= ?k => 
      apply max_le; split
  | H : Nat.max ?n ?m < ?k |- _ =>
      let A := fresh "A" in
      let A' := fresh "A" in 
      assert (A: n < k) by lia;
      assert (A': m < k) by lia;
      clear H
  | H : Nat.max ?n ?m <= ?k |- _ =>
      let A := fresh "A" in
      let A' := fresh "A" in 
      assert (A: n <= k) by lia;
      assert (A': m <= k) by lia;
      clear H
  | H: Nat.max ?n ?m = ?k |- _ =>
      let A := fresh "A" in 
      assert (n = k \/ m = k) as [A | A] by lia;
      clear H
  | H: S ?n <= S ?m |- _ =>
      (* idtac "simpl 0"; *)
      let a := fresh "A" in
      assert (a: n <= m) by lia;
      clear H
  | H: S ?n < S ?m |- _ =>
      (* idtac "simpl 0"; *)
      let a := fresh "A" in
      assert (a: n < m) by lia;
      clear H
  | H: ?n + 1 < S ?m |- _ =>
      (* idtac "simpl 1"; *)
      let a := fresh "A" in
      assert (a: n < m) by lia;
      clear H
  | H: ?n + ?k < ?m + ?k |- _ =>
      (* idtac "simpl 2"; *)
      let a := fresh "A" in
      assert (a: n < m) by lia;
      clear H
  | H: ?n + ?m < ?n + ?k |- _ =>
      (* idtac "simpl 3"; *)
      let a := fresh "A" in
      assert (a: m < k) by lia;
      clear H
  | H: ?n + ?m < ?n + ?k + ?l |- _ =>
      (* idtac "simpl 4"; *)
      let a := fresh "A" in
      assert (a: m < k + l) by lia;
      clear H
  | _ : context[?n + (?m + ?l)] |- _ => 
      (* idtac "simpl 5"; *)
      let e := fresh "E" in
      assert (e:n + (m + l) = n + m + l) by lia;
      rewrite e in *; clear e
  | |- context[?n + (?m + ?l)] => 
      (* idtac "simpl 6"; *)
      let e := fresh "E" in
      assert (e:n + (m + l) = n + m + l) by lia;
      rewrite e in *; clear e
  | H: ~ ?n < ?m |- _ =>
      (* idtac "simpl 7"; *)
      let e := fresh "E" in
      let n' := fresh n in
      assert (e: n = m + (n - m)) by lia;
      rewrite e in *; clear e H;
      set (n' := n - m) in *
  | H: context[?n + 0] |- _ => 
      (* idtac "simpl 8"; *)
      let e := fresh "E" in
      assert (e: n + 0 = n) by lia;
      rewrite e in *; clear e
  | [|- context[?n + 0]] => 
      (* idtac "simpl 9"; *)
      let e := fresh "E" in
      assert (e: n + 0 = n) by lia;
      rewrite e in *; clear e
  | H: context[0 + ?n] |- _ => 
      (* idtac "simpl 10"; *)
      let e := fresh "E" in
      assert (e: 0 + n = n) by lia;
      rewrite e in *; clear e
  | [|- context[0 + ?n]] => 
      (* idtac "simpl 11"; *)
      let e := fresh "E" in
      assert (e: 0 + n = n) by lia;
      rewrite e in *; clear e
  | |- _ => 
      (* idtac "trying lia";  *)
      lia
  end.

Ltac clear_dup := 
  match goal with
  | H : ?t, H' : ?t |- _ => clear H'
  end.

Ltac invert_constr := 
  match goal with
  | H : ?C _ = ?C _ |- _ => is_constructor C; invert H
  | H : ?C _ _ = ?C _ _ |- _ => is_constructor C; invert H
  | H : ?C _ _ _ = ?C _ _ _ |- _ => is_constructor C; invert H
  | H : ?C _ _ _ _ = ?C _ _ _ _ |- _ => is_constructor C; invert H
  | H : ?C _ _ _ _ _ = ?C _ _ _ _ _ |- _ => is_constructor C; invert H
  | H : ?C _ _ _ _ _ _ = ?C _ _ _ _ _ _ |- _ => is_constructor C; invert H
  end.

Ltac reduce := repeat (
  intros || split || (cbn in *) || subst || subst_all
  || intuition auto || congruence
  || clear_dup || invert_constr
  || destruct_exist_H || destruct_and_H).

#[global]
Hint Extern 100 => reduce: reduce.

Ltac destruct_match :=
  match goal with 
  | [|- context[match ?e with _ => _ end]] => 
    let freshE := fresh "E" in
      destruct e eqn:freshE
  | [_:context[match ?e with _ => _ end] |- _] => 
    let freshE := fresh "E" in
      destruct e eqn:freshE
  end.

(* Taken from https://github.com/epfl-lara/SystemFR/blob/master/Tactics.v *)
Ltac isThere P := match goal with
  | H: ?Q |- _ => unify P Q
(*  | |- ?Q => unify P Q *)
  end.

Ltac termNotThere p :=
  let P := type of p in
    tryif (isThere P) then fail else idtac.

Ltac poseNew E := termNotThere E; pose proof E.

(* Marking contexts to avoid applying the same step twice *)
(* Used to ensure termination of some tactics *)
Inductive Marked {T}: T -> string -> Type :=
| Mark: forall t s, Marked t s
.

Ltac clear_marked :=
  repeat match goal with
          | H: Marked _ _ |- _ => clear H
          end.

Notation "'internal'" := (Marked _ _) (at level 50).
  
Ltac apply_any :=
  match goal with
  | H: _ |- _ => apply H
  end.

Ltac rewrite_any :=
  match goal with
  | H: _ |- _ => rewrite H in *
  end.

Ltac erewrite_any :=
  match goal with
  | H: _ |- _ => erewrite H in *
  end.

Ltac rewrite_back_any :=
  match goal with
  | H: _ |- _ => rewrite <- H in *
  end.

Ltac eapply_any :=
  match goal with
  | H: _ |- _ => eapply H
  end.

Ltac apply_anywhere f :=
  match goal with
  | H: _ |- _ => apply f in H
  end.

Ltac eapply_anywhere f :=
  match goal with
  | H: _ |- _ => eapply f in H
  end.

Ltac rewrite_anywhere f :=
  match goal with
  | H: _ |- _ => rewrite f in H
  end.

Ltac erewrite_anywhere f :=
  match goal with
  | H: _ |- _ => erewrite f in H
  end.

Ltac instantiate_any :=
  match goal with
  | H1: forall x, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1, H2) "instantiation");
    pose proof (H1 _ H2)
  | H1: forall x y, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1, H2) "instantiation");
    pose proof (H1 _ _ H2)
  | H1: forall x y z, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1, H2) "instantiation");
    pose proof (H1 _ _ _ H2)
  end.
