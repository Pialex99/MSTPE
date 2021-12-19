From Utils Require Import Tactics Env.
From CPS Require Import Tree Fun_sem.

Reserved Notation "v1 '≡ᵥ' v2 '@' k" (at level 70, no associativity).
Reserved Notation "r1 '≡ᵣ' r2 '@' k" (at level 70, no associativity).

Inductive equiv_v : nat -> value -> value -> Prop := 
  | equiv_lit : forall k l, Lit l ≡ᵥ Lit l @ k 
  | equiv_tuple : forall k v1 v1' v2 v2', 
      v1 ≡ᵥ v2 @ k -> v1' ≡ᵥ v2' @ k -> Tuple v1 v1' ≡ᵥ Tuple v2 v2' @ k
  | equiv_left : forall k v1 v2, 
      v1 ≡ᵥ v2 @ k -> Left v1 ≡ᵥ Left v2 @ k
  | equiv_right : forall k v1 v2, 
      v1 ≡ᵥ v2 @ k -> Right v1 ≡ᵥ Right v2 @ k
  | equiv_fun : forall k n1 c1 a1 b1 Γ1 n2 c2 a2 b2 Γ2,
      let f1 := Fnt n1 c1 a1 b1 in 
      let f2 := Fnt n2 c2 a2 b2 in 
      (forall k' io io1 io2 v ac bc Γc Γcnt r1 r2, k' < k -> 
        let cnt1 := Cnt1 c1 ac bc in
        let cnt2 := Cnt1 c2 ac bc in
        evalₜ k' (Γ1 + (n1, Fun f1 Γ1) + (a1, v)) (empty + (c1, Cnt cnt1 Γc Γcnt)) b1 io = (r1, io1) -> 
        evalₜ k' (Γ2 + (n2, Fun f2 Γ2) + (a2, v)) (empty + (c2, Cnt cnt2 Γc Γcnt)) b2 io = (r2, io2) -> 
          r1 ≡ᵣ r2 @ k' /\ io1 = io2) -> 
        Fun f1 Γ1 ≡ᵥ Fun f2 Γ2 @ k
with equiv_r : nat -> result -> result -> Prop :=
  | equiv_halt : forall k v1 v2, 
      v1 ≡ᵥ v2 @ k -> Rhalt v1 ≡ᵣ Rhalt v2 @ k
  | equiv_err : forall k, Rerr ≡ᵣ Rerr @ k
  | equiv_eoi : forall k, Reoi ≡ᵣ Reoi @ k
  | equiv_timeout : forall k, Rtimeout ≡ᵣ Rtimeout @ k
where "v1 '≡ᵥ' v2 '@' k" := (equiv_v k v1 v2) and
      "r1 '≡ᵣ' r2 '@' k" := (equiv_r k r1 r2).

#[global]
Hint Constructors equiv_v equiv_r : equiv_cps.

Lemma equiv_fun_0 : forall f1 Γ1 f2 Γ2, 
  Fun f1 Γ1 ≡ᵥ Fun f2 Γ2 @ 0.
Proof.
  intros; destruct f1, f2; constructor; intros; lia.
Qed.

Lemma equiv_refl_ind : forall k k', k' <= k -> forall r v, r ≡ᵣ r @ k' /\ v ≡ᵥ v @ k'.
Proof with repeat reduce; auto using equiv_fun_0 with equiv_cps.
  induction k; split.
  - (* r 0 *) 
    destruct k'; try lia.
    induction r...
    constructor.
    induction v0...
  - (* v 0 *)
    destruct k'; try lia.
    induction v...
  - (* r S k *)
    induction r...
    constructor.
    induction v0...
    destruct f; constructor...
    rewrite H1 in H2...
    unshelve epose proof (IHk k'0 _ r2 v) as [H2 _]; auto with lia.
  - (* v S k *)
    induction v...
    destruct f; constructor...
    rewrite H1 in H2...
    unshelve epose proof (IHk k'0 _ r2 v) as [H2 _]; auto with lia.
Qed.

Corollary equiv_v_refl : forall k v, v ≡ᵥ v @ k.
Proof.
  intros.
  unshelve epose proof equiv_refl_ind k k _ Rtimeout v as [_ H']; 
  auto with lia.
Qed.

Corollary equiv_r_refl : forall k r, r ≡ᵣ r @ k.
Proof.
  intros.
  unshelve epose proof equiv_refl_ind k k _ r (Lit UnitLit) as [H' _]; 
  auto with lia.
Qed.

#[global]
Hint Resolve equiv_r_refl equiv_v_refl : equiv_cps.

Lemma equiv_v_sym_0 : forall v1 v2, v1 ≡ᵥ v2 @ 0 -> v2 ≡ᵥ v1 @ 0.
Proof with auto with equiv_cps.
  induction v1, v2; inversion 1...
  constructor; simpl_lia.
Qed.

Lemma equiv_r_sym_ind : forall k r1 r2, 
  r1 ≡ᵣ r2 @ k -> 
  (forall v1 v2, v1 ≡ᵥ v2 @ k -> v2 ≡ᵥ v1 @ k) -> 
    r2 ≡ᵣ r1 @ k.
Proof with auto using equiv_v_sym_0 with equiv_cps.
  induction k; inversion 1; subst...
Qed.

Lemma equiv_v_sym_ind : forall k v1 v2, 
  v1 ≡ᵥ v2 @ k ->
  (forall k', k' < k -> forall r1 r2, r1 ≡ᵣ r2 @ k' -> r2 ≡ᵣ r1 @ k') ->
    v2 ≡ᵥ v1 @ k.
Proof with eauto using equiv_v_sym_0, equiv_r_sym_ind with equiv_cps.
  induction k...
  induction v1, v2; inversion 1; 
  repeat reduce...
  constructor; repeat reduce.
  all: specialize (H2 _ _ _ _ _ _ _ _ _ _ _ H0 H3 H1) as [Hr Hio]...
Qed.

Lemma equiv_sym_ind : forall k, 
  (forall k', k' <= k -> forall v1 v2, v1 ≡ᵥ v2 @ k' -> v2 ≡ᵥ v1 @ k') /\ 
  (forall k', k' <= k -> forall r1 r2, r1 ≡ᵣ r2 @ k' -> r2 ≡ᵣ r1 @ k').
Proof with auto using equiv_v_sym_0, equiv_r_sym_ind, equiv_v_sym_ind with equiv_cps lia.
  induction k...
  destruct IHk as [IHv Ihr].
  split; destruct k'...
Qed.

Corollary equiv_v_sym : forall k v1 v2, 
  v1 ≡ᵥ v2 @ k -> v2 ≡ᵥ v1 @ k.
Proof with eauto with lia.
  intros.
  pose proof (equiv_sym_ind (S k)) as [Hv Hr]...
Qed.

Corollary equiv_r_sym : forall k r1 r2, 
  r1 ≡ᵣ r2 @ k -> r2 ≡ᵣ r1 @ k.
Proof with eauto with lia.
  intros.
  pose proof (equiv_sym_ind (S k)) as [Hv Hr]...
Qed.

#[global]
Hint Resolve equiv_r_sym equiv_v_sym : equiv_cps.

Lemma equiv_v_trans_0 : forall v1 v2 v3, v1 ≡ᵥ v2 @ 0 -> v2 ≡ᵥ v3 @ 0 -> v1 ≡ᵥ v3 @ 0.
Proof with eauto with equiv_cps lia.
  induction v1, v2, v3; inversion 1; inversion 1; subst...
  constructor...
Qed.

Lemma equiv_r_trans_ind : forall k r1 r2 r3, 
  r1 ≡ᵣ r2 @ k -> r2 ≡ᵣ r3 @ k -> 
  (forall v1 v2 v3, v1 ≡ᵥ v2 @ k -> v2 ≡ᵥ v3 @ k -> v1 ≡ᵥ v3 @ k) ->
    r1 ≡ᵣ r3 @ k.
Proof with eauto using equiv_v_trans_0 with equiv_cps lia.
  induction k, r1, r2, r3; inversion 1; inversion 1; subst...
Qed.

Lemma equiv_v_trans_ind : forall k v1 v2 v3, 
  v1 ≡ᵥ v2 @ k -> v2 ≡ᵥ v3 @ k -> 
  (forall k', k' < k -> forall r1 r2 r3, r1 ≡ᵣ r2 @ k' -> r2 ≡ᵣ r3 @ k' -> r1 ≡ᵣ r3 @ k') ->
    v1 ≡ᵥ v3 @ k.
Proof with eauto 4 using equiv_v_trans_0, equiv_r_trans_ind with equiv_cps lia.
  induction k...
  induction v1, v2, v3; inversion 1; inversion 1; repeat reduce...
  constructor; repeat reduce.
  all: destruct (evalₜ k' (e0 + (n2, Fun (Fnt n2 c2 a2 b2) e0) + (a2, v)) 
                ({ } + (c2, Cnt (Cnt1 c2 ac bc) Γc Γcnt)) b2 io) as [r0 io0] eqn:E.
  all: specialize (H2 _ _ _ _ _ _ _ _ _ _ _ H0 H1 E) as [Hr Hio]; 
       specialize (H9 _ _ _ _ _ _ _ _ _ _ _ H0 E H3) as [Hr' Hio']; 
       repeat reduce...
Qed.

Lemma equiv_trans_ind : forall k,
  (forall k', k' <= k -> forall v1 v2 v3, v1 ≡ᵥ v2 @ k' -> v2 ≡ᵥ v3 @ k' -> v1 ≡ᵥ v3 @ k') /\
  (forall k', k' <= k -> forall r1 r2 r3, r1 ≡ᵣ r2 @ k' -> r2 ≡ᵣ r3 @ k' -> r1 ≡ᵣ r3 @ k').
Proof with eauto 4 using equiv_v_trans_0, equiv_r_trans_ind, equiv_v_trans_ind with equiv_cps lia.
  induction k; split...
  all: destruct IHk as [IHv IHr].
  all: destruct k'...
Qed.

Corollary equiv_v_trans : forall k v1 v2 v3, 
  v1 ≡ᵥ v2 @ k -> v2 ≡ᵥ v3 @ k -> v1 ≡ᵥ v3 @ k.
Proof with eauto.
  intros.
  specialize (equiv_trans_ind k) as [Hv _]...
Qed.

Corollary equiv_r_trans : forall k r1 r2 r3, 
  r1 ≡ᵣ r2 @ k -> r2 ≡ᵣ r3 @ k -> r1 ≡ᵣ r3 @ k.
Proof with eauto.
  intros.
  specialize (equiv_trans_ind k) as [_ Hr]...
Qed.

#[global]
Hint Resolve equiv_v_trans equiv_r_trans : equiv_cps.
