Require Export PeanoNat Nat List.
Require Import Lia.
From Utils Require Import Tactics.

Open Scope nat_scope.
Open Scope list_scope.

(* In an environment the tuples are kept in increasing order with respect to the key *)
(* We do so to have a unique representation for each mapping *)
Definition env (A: Type) : Type := list (nat * A).

Declare Scope env_scope.
Open Scope env_scope.

Definition empty {A: Type} : env A := nil.
Notation "'{' '}'" := empty : env_scope.

Fixpoint lookup {A: Type} (e : env A) (n: nat) : option A :=
  match e with 
  | nil => None 
  | (n', a') :: t => 
    if (n =? n') then Some a'
    else lookup t n
  end.
Notation "env '?' k" := (lookup env k) 
  (at level 60, no associativity) : env_scope.

Fixpoint add {A: Type} (e : env A) (n: nat) (a: A) : env A := 
  match e with
  | nil => (n, a) :: nil
  | (n', a') :: t =>
      if (n =? n') then (n, a) :: t
      else if (n <? n') then (n, a) :: e
      else (n', a') :: add t n a
  end.
Notation "env '+' '(' k ',' v ')'" := (add env k v) 
  (at level 40, left associativity) : env_scope.

Fixpoint update {A: Type} (e1 e2 : env A) : env A :=
  match e2 with
  | nil => e1 
  | (n, a) :: e2 =>
      (update e1 e2) + (n, a)
  end.
Notation "env1 '<++>' env2" := (update env1 env2)
  (at level 50, left associativity) : env_scope.

Fixpoint max {A: Type} (e : env A) : option nat :=
  match e with 
  | nil => None
  | (n, _) :: env =>
      match env with 
      | nil => Some n
      | (n', _) :: _ => 
          option_map (Nat.max n) (max env)
      end
  end.

Fixpoint min {A: Type} (e : env A) : option nat :=
  match e with 
  | nil => None
  | (n, _) :: env =>
      match env with 
      | nil => Some n
      | (n', _) :: _ => 
          option_map (Nat.min n) (min env)
      end
  end.

Fixpoint well_ordered {A: Type} (e : env A) {struct e} : Prop :=
  match e with
  | nil => True 
  | (n1, a1) :: e => 
      match e with
      | nil => True
      | (n2, a2) :: _ => 
          if n1 <? n2 then well_ordered e 
          else False
      end
  end.

Theorem lookup_empty: forall A k, (@empty A) ? k = None.
Proof. auto. Qed.

Theorem lookup_add_eq: forall A (e : env A) n v,
    (e + (n, v)) ? n = Some v.
Proof.
  induction e; repeat reduce || destruct_match.
  all: rewrite Nat.eqb_refl in *; discriminate.
Qed.

Theorem lookup_add_ne: forall A (e : env A) n1 n2 v,
  n1 <> n2 ->
    (e + (n1, v)) ? n2 = e ? n2.
Proof.
  induction e; repeat reduce || destruct_match.
  all: repeat rewrite Nat.eqb_eq in *; subst; auto with exfalso.
Qed.

Theorem add_com : forall A (e : env A) n1 n2 a1 a2, n1 <> n2 ->
  e + (n1, a1) + (n2, a2) = e + (n2, a2) + (n1, a1).
Proof.
  Opaque Nat.ltb.
  induction e; repeat reduce || destruct_match.
  all: repeat rewrite Nat.eqb_eq in * 
           || rewrite Nat.eqb_neq in * 
           || rewrite Nat.ltb_lt in * 
           || rewrite Nat.ltb_ge in *; 
        subst; auto with exfalso lia.
  f_equal; auto.
Qed.  

Corollary lookup_add_com : forall A (env : env A) n n1 n2 v1 v2, n1 <> n2 ->
  env + (n1, v1) + (n2, v2) ? n = env + (n2, v2) + (n1, v1) ? n.
Proof.
  intros.
  rewrite add_com; auto.
Qed.

Theorem add_dup : forall A (e : env A) n a a', 
  e + (n, a) + (n, a') = e + (n, a').
Proof.
  induction e; repeat reduce || destruct_match.
  all: repeat rewrite Nat.eqb_eq in * 
           || rewrite Nat.eqb_refl in *
           || rewrite Nat.ltb_lt in * 
           || rewrite Nat.ltb_ge in *;
       subst; auto with lia.
Qed.

Corollary lookup_add_dup : forall A (env : env A) n n' v1 v2, 
  env + (n, v1) + (n, v2) ? n' = env + (n, v2) ? n'.
Proof.
  intros.
  rewrite add_dup; auto.
Qed.

Theorem lookup_concat_not_found: forall A (e1 e2 : env A) n,
  (e1 ? n = None) -> (e2 ? n = None) -> (e2 <++> e1) ? n = None.
Proof.
  induction e1; repeat reduce || destruct_match.
  rewrite Nat.eqb_neq in *.
  rewrite lookup_add_ne; auto.
Qed.

Theorem lookup_concat_not_found': forall A (e1 e2 : env A) n,
   (e2 <++> e1) ? n = None -> (e1 ? n = None) /\ (e2 ? n = None).
Proof.
  induction e1; repeat reduce || destruct_match.
  all: repeat rewrite Nat.eqb_eq in * 
           || rewrite Nat.eqb_refl in *
           || rewrite Nat.eqb_neq in *
           || rewrite Nat.ltb_lt in * 
           || rewrite Nat.ltb_ge in *;
       subst; auto with lia.
  - rewrite lookup_add_eq in H; auto.
  - rewrite lookup_add_ne in H; auto.
    apply IHe1 in H as [? ?]; auto.
  - destruct (Nat.eq_dec n n0); subst.
    * rewrite lookup_add_eq in H; auto.
      discriminate.
    * rewrite lookup_add_ne in H; auto.
      apply IHe1 in H as [? ?]; auto.
Qed.

Theorem lookup_concat_first: forall A (e1 e2 : env A) n v,
  e1 ? n = Some v -> (e2 <++> e1) ? n = Some v.
Proof.
  induction e1; repeat reduce || destruct_match.
  all: rewrite Nat.eqb_eq in E || rewrite Nat.eqb_neq in E; 
       subst; auto using lookup_add_eq.
  rewrite lookup_add_ne; auto.
Qed.

Theorem lookup_concat_second: forall A (e1 e2 : env A) n,
  e1 ? n = None -> (e2 <++> e1) ? n = e2 ? n.
Proof.
  induction e1; repeat reduce || destruct_match.
  rewrite lookup_add_ne; auto.
  rewrite Nat.eqb_neq in E.
  intro; subst; lia.
Qed.

Theorem lookup_concat_found: forall A (e1 e2 : env A) n v,
  (e2 <++> e1) ? n = Some v -> (e1 ? n = Some v) \/ (e1 ? n = None /\ e2 ? n = Some v).
Proof.
  induction e1; repeat reduce || destruct_match.
  - rewrite Nat.eqb_eq in E; subst.
    rewrite lookup_add_eq in H.
    auto.
  - rewrite Nat.eqb_neq in E.
    rewrite lookup_add_ne in H; auto.
Qed.

Lemma update_add: forall A (e : env A) n v,
  e <++> ({ } + (n, v)) = e + (n, v).
Proof. auto. Qed.
  
Lemma add_update: forall A (e1 e2 : env A) n v,
  (e1 <++> e2) + (n, v) = e1 <++> (e2 + (n, v)).
Proof.
  induction e2; repeat reduce || destruct_match.
  - rewrite Nat.eqb_eq in E; subst.
    auto using add_dup.
  - rewrite Nat.eqb_neq in E.
    rewrite <- IHe2.
    auto using add_com.
Qed.

Lemma update_empty: forall A (e : env A),
  e <++> { } = e.
Proof. auto. Qed.

Lemma update_empty': forall A (e : env A),
  well_ordered e -> { } <++> e = e.
Proof.
  induction e; reduce.
  repeat destruct_match; reduce.
  apply IHe in H.
  rewrite H.
  reduce.
  rewrite E2.
  destruct_match; reduce.
  rewrite Nat.eqb_eq in E; rewrite Nat.ltb_lt in E2.
  lia.
Qed.

Lemma min_max : forall A (e : env A) m M,
  min e = Some m -> 
  max e = Some M ->
    m <= M.
Proof. 
  induction e; reduce.
  repeat destruct_match; reduce.
  unfold option_map in *.
  destruct l eqn:E.
  - repeat invert_constr.
    lia.
  - repeat destruct_match; reduce.
    lia.
Qed.

Lemma well_ordered_append : forall A (e : env A) M n a, 
  well_ordered e -> 
  max e = Some M -> 
  M < n -> 
    e + (n, a) = e ++ (n, a) :: nil.
Proof.
  induction e; reduce.
  destruct a, e; reduce.
  - assert (n <> M) by lia. 
    apply Nat.eqb_neq in H0.
    rewrite H0.
    assert (~ n < M) by lia.
    apply Nat.ltb_nlt in H2.
    rewrite H2.
    reflexivity.
  - destruct p, (n0 <? n1) eqn:E; reduce.
    destruct (
      match e with
      | nil => Some n1
      | p :: _ => 
          let (_, _) := p in
          option_map (Nat.max n1) (max e)
      end
    ); reduce.
    assert (n <> n0) by lia.
    apply Nat.eqb_neq in H0.
    rewrite H0.
    assert (~ n < n0) by lia.
    apply Nat.ltb_nlt in H2.
    rewrite H2.
    rewrite (IHe _ _ _ H eq_refl); auto with lia.
Qed.

Lemma well_ordered_prepend : forall A (e : env A) m n a, 
  well_ordered e -> 
  min e = Some m ->
  n < m -> 
    e + (n, a) = (n, a) :: e.
Proof. 
  destruct e; reduce.
  destruct p, e; reduce.
  - assert (n <> m) by lia.
    apply Nat.eqb_neq in H0.
    rewrite H0.
    apply Nat.ltb_lt in H1.
    rewrite H1.
    auto.
  - destruct p. 
    destruct (n0 <? n1); reduce.
    destruct (
      match e with
      | nil => Some n1
      | p :: _ =>
          let (_, _) := p in
          option_map (Nat.min n1) (min e)
      end); reduce.
    assert (n <> n0) by lia.
    apply Nat.eqb_neq in H0.
    rewrite H0.
    assert (n < n0) by lia.
    apply Nat.ltb_lt in H2.
    rewrite H2.
    auto.
Qed.

Lemma well_ordered_concat : forall A (e1 e2 : env A) M m n a, 
  well_ordered e1 -> 
  well_ordered e2 -> 
  max e1 = Some M -> 
  min e2 = Some m -> 
  M < n -> n < m ->
    (e1 ++ e2) + (n, a) = e1 ++ (n, a) :: e2.
Proof.
  induction e1; reduce.
  destruct a, e1; reduce.
  - assert (n <> M) by lia.
    apply Nat.eqb_neq in H1.
    rewrite H1.
    assert (~ n < M) by lia.
    apply Nat.ltb_nlt in H5.
    rewrite H5.
    erewrite well_ordered_prepend; eauto with lia.
  - destruct p.
    destruct (n0 <? n1) eqn:E; reduce.
    destruct (
      match e1 with
      | nil => Some n1
      | p :: _ => 
          let (_, _) := p in
          option_map (Nat.max n1) (max e1)
      end
    ); reduce.
    assert (n <> n0) by lia.
    apply Nat.eqb_neq in H1.
    rewrite H1.
    assert (~ n < n0) by lia.
    apply Nat.ltb_nlt in H5.
    rewrite H5.
    rewrite (IHe1 _ _ _ _ _ H H0 eq_refl H2); auto with lia.
Qed.

Lemma well_ordered_min : forall A (e : env A) n a,
  well_ordered ((n, a) :: e) -> 
    min ((n, a) :: e) = Some n.
Proof.
  induction e; reduce.
  destruct a, (n <? n0) eqn:E; reduce.
  rewrite (IHe _ a H); reduce; f_equal.
  apply Nat.ltb_lt in E; lia.
Qed.

Lemma well_ordered_min_max: forall A (e1 e2 : env A) m M,
  well_ordered e1 -> 
  well_ordered e2 -> 
  max e1 = Some M ->
  min e2 = Some m -> 
  M < m ->
    e1 <++> e2 = e1 ++ e2.
Proof.
  induction e2; reduce.
  repeat destruct_match; reduce.
  eauto using well_ordered_append.
  destruct (
    match l with
    | nil => Some n0
    | p :: _ =>
        let (_, _) := p in
        option_map (Nat.min n0) (min l)
    end); reduce.
  rewrite (IHe2 _ _ H H0 H1 eq_refl); auto with lia.
  apply Nat.ltb_lt in E2.
  apply (well_ordered_concat _ _ _ M n0 _ _ H); try solve [reduce].
  eapply well_ordered_min; reduce.
  lia.
Qed.

Ltac env := 
  match goal with
  | H: (_ <++> _) ? _ = None |- _ => 
    let H1 := fresh "H" in 
    let H2 := fresh "H" in 
    apply lookup_concat_not_found' in H as [H1 H2]
  | H1: ?e1 ? ?n = None,
    H2: ?e2 ? ?n = None |- _ =>
    poseNew (Mark (e1, e2, n) "lookup_concat_not_found");
    pose proof (lookup_concat_not_found _ _ _ _ H1 H2)
  | [H: context[_ <++> { }] |- _ ] =>
    rewrite update_empty in H
  | [|- context[_ <++> { }]] =>
    rewrite update_empty
  | [H: context[{ } <++> _] |- _ ] =>
    rewrite update_empty' in H
  | [|- context[{ } <++> _]] =>
    rewrite update_empty'
  | [H: context[(_ <++> _) + (_, _)] |- _ ] => 
    rewrite add_update in H
  | [|- context[(_ <++> _) + (_, _)]] => 
    rewrite add_update
  | [H: context[_ <++> ({ } + (_, _))] |- _ ] =>
    rewrite update_add in H
  | [|- context[_ <++> ({ } + (_, _))]] =>
    rewrite update_add
  | [H: context[{ } ? _] |- _ ] => 
    rewrite lookup_empty in H
  | [|- context[{ } ? _]] => 
    rewrite lookup_empty
  | [H: context[(_ + (?n, _)) ? ?n] |- _ ] => 
    rewrite lookup_add_eq in H
  | [|- context[(_ + (?n, _)) ? ?n]] => 
    rewrite lookup_add_eq
  | [H: ?n1 <> ?n2 |- context[(_ + (?n1, _)) ? ?n2]] => 
    rewrite (lookup_add_ne _ _ _ _ _ H)
  | [H: ?n1 <> ?n2, 
     H': context[(_ + (?n1, _)) ? ?n2] |- _ ] => 
    rewrite (lookup_add_ne _ _ _ _ _ H) in H'
  | [H: context[(_ + (?n, _) + (?n, _))] |- _ ] => 
    rewrite add_dup in H
  | [|- context[(_ + (?n, _) + (?n, _))]] => 
    rewrite add_dup
  | [H: ?n1 <> ?n2 |- context[(_ + (?n1, _) + (?n2, _))]] => 
    rewrite (add_com _ _ _ _ _ _ _ H)
  | [H: ?n1 <> ?n2, 
     H': context[(_ + (?n1, _) + (?n2, _))] |- _ ] => 
    rewrite (add_com _ _ _ _ _ _ _ H) in H'
  | [|- context[(?e2 <++> ?e1) ? ?n]] => 
    let E := fresh "E" in 
    destruct (e1 ? n) eqn:E;
    [rewrite (lookup_concat_first _ _ _ _ _ E) 
    | rewrite (lookup_concat_second _ _ _ _ E)]
  | [H: context[(?e2 <++> ?e1) ? ?n] |- _ ] => 
    let E := fresh "E" in 
    destruct (e1 ? n) eqn:E;
    [rewrite (lookup_concat_first _ _ _ _ _ E) in H
    | rewrite (lookup_concat_second _ _ _ _ E) in H]
  | [|- context[(_ + (?n1, _) + (?n2, _))]] => 
    destruct (Nat.eq_dec n1 n2); 
    [subst; rewrite add_dup | rewrite add_com; auto]
  | [|- context[(_ + (?n1, _)) ? ?n2]] =>
    destruct (Nat.eq_dec n1 n2); 
    [subst; rewrite lookup_add_eq | rewrite lookup_add_ne; auto]
  | [H: context[(_ + (?n1, _) + (?n2, _))] |- _ ] => 
    destruct (Nat.eq_dec n1 n2); 
    [subst; rewrite add_dup in H | rewrite add_com in H; auto]
  | [H: context[(_ + (?n1, _)) ? ?n2] |- _ ] =>
    destruct (Nat.eq_dec n1 n2); 
    [subst; rewrite lookup_add_eq in H | rewrite lookup_add_ne in H; auto]
  end.

Global Opaque empty lookup add update.