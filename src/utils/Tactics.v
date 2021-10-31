Require Export Lia.

#[global]
Hint Extern 50 => lia: lia.

Ltac destruct_exist :=
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

Ltac invert H := inversion H; subst.

Ltac simpl_lia :=
  match goal with 
  | H: ?n + 1 < ?m + 1 |- _ =>
      let a := fresh "A" in
      assert (a: n < m) by lia;
      clear H
  | H: ?n + ?m < ?n + ?k |- _ =>
      let a := fresh "A" in
      assert (a: m < k) by lia;
      clear H
  | H: ?n + ?m < ?n + ?k + ?l |- _ =>
      let a := fresh "A" in
      assert (a: m < k + l) by lia;
      clear H
  | _ : context[?n + (?m + ?l)] |- _ => 
      let e := fresh "E" in
      assert (e:n + (m + l) = n + m + l) by lia;
      rewrite e in *; clear e
  | |- context[?n + (?m + ?l)] => 
      let e := fresh "E" in
      assert (e:n + (m + l) = n + m + l) by lia;
      rewrite e in *; clear e
  | H: ~ ?n < ?m |- _ =>
      let e := fresh "E" in
      let n' := fresh n in
      assert (e: n = m + (n - m)) by lia;
      rewrite e in *; clear e H;
      set (n' := n - m) in *
  | |- _ => lia
  end.

Ltac reduce :=
  intros || (cbn in *) || subst 
  || intuition congruence 
  || destruct_exist || destruct_and_H.

Ltac destruct_match :=
  match goal with 
  | [|- context[if ?e then _ else _]] => 
    let freshE := fresh "E" in
      destruct e eqn:freshE
  | [|- context[match ?e with _ => _ end]] => 
    let freshE := fresh "E" in
      destruct e eqn:freshE
  | [_:context[if ?e then _ else _] |- _] => 
    let freshE := fresh "E" in
      destruct e eqn:freshE
  | [_:context[match ?e with _ => _ end] |- _] => 
    let freshE := fresh "E" in
      destruct e eqn:freshE
  end.

Ltac apply_anywhere f :=
  match goal with 
  | H:_ |- _ => apply f in H
  end. 