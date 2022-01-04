From Utils Require Import Tactics Env.
From CPS Require Import Tree Fun_sem.

(* (* Section Term_rel.
  Variable val_rel : nat -> value -> value -> Prop.

  Definition res_rel' (k : nat) (r1 r2 : result): Prop := 
    match r1, r2 with 
    | Rtimeout, Rtimeout => True
    | Rerr, Rerr => True
    | Reoi, Reoi => True
    | Rhalt v1, Rhalt v2 => val_rel k v1 v2 
    | _, _ => False
    end.

  Definition term_rel' (k : nat) (e1 e2 : env value * env cntV * term): Prop :=
    let '(Γ1, Γc1, t1) := e1 in 
    let '(Γ2, Γc2, t2) := e2 in 
      forall k' io io1 io2 r1 r2, k' < k -> 
        evalₜ k' Γ1 Γc1 t1 io = (r1, io1) -> 
        evalₜ k' Γ2 Γc2 t2 io = (r2, io2) ->
          res_rel' (k - k') r1 r2 /\ io1 = io2.
End Term_rel.

Section Cnt_rel.
  Variable val_rel : nat -> value -> value -> Prop.

  Definition cnt_rel' (k : nat) (cnt1 cnt2 : cntV) : Prop :=
    match cnt1, cnt2 with
    | Cnt (Cnt0 n1 b1) Γ1 Γc1, Cnt (Cnt0 n2 b2) Γ2 Γc2 => 
        let Γc1' := Γc1 + (n1, cnt1) in 
        let Γc2' := Γc2 + (n2, cnt2) in 
        term_rel' val_rel k (Γ1, Γc1', b1) (Γ2, Γc2', b2)
    | Cnt (Cnt1 n1 a1 b1) Γ1 Γc1, Cnt (Cnt1 n2 a2 b2) Γ2 Γc2 => 
        forall v1 v2, val_rel k v1 v2 -> 
          let Γ1' := Γ1 + (a1, v1) in 
          let Γc1' := Γc1 + (n1, cnt1) in 
          let Γ2' := Γ2 + (a2, v2) in 
          let Γc2' := Γc2 + (n2, cnt2) in 
          term_rel' val_rel k (Γ1', Γc1', b1) (Γ2', Γc2', b2)
    | _ , _ => False
    end.
End Cnt_rel.

Fixpoint val_rel (k : nat) (v1 v2 : value) {struct k}: Prop :=
  let fix val_rel_aux (v1 v2 : value) {struct v1}: Prop :=
    match v1, v2 with
    | Lit l1, Lit l2 => l1 = l2
    | Tuple v1_1 v1_2, Tuple v2_1 v2_2 =>
        val_rel_aux v1_1 v2_1 /\ val_rel_aux v1_2 v2_2
    | Left v1, Left v2 =>
        val_rel_aux v1 v2
    | Right v1, Right v2 =>
        val_rel_aux v1 v2
    | Fun (Fnt n1 c1 a1 b1) Γ1, Fun (Fnt n2 c2 a2 b2) Γ2 =>
        match k with
        | 0 => True 
        | S k' => 
            forall v1' v2' ac1 bc1 Γc1 Γcnt1 ac2 bc2 Γc2 Γcnt2,
              let cnt1 := Cnt (Cnt1 c1 ac1 bc1) Γc1 Γcnt1 in
              let cnt2 := Cnt (Cnt1 c2 ac2 bc2) Γc2 Γcnt2 in
              let Γ1' := Γ1 + (n1, v1) + (a1, v1') in
              let Γ2' := Γ2 + (n2, v2) + (a2, v2') in
              let Γc1' := empty + (c1, cnt1) in
              let Γc2' := empty + (c2, cnt2) in
              val_rel k' v1' v2' ->
              cnt_rel' val_rel k' cnt1 cnt2 -> 
                term_rel' val_rel k' (Γ1', Γc1', b1) (Γ2', Γc2', b2)
        end
    | _, _ => False
    end
  in val_rel_aux v1 v2.

Notation res_rel := (res_rel' val_rel).

Notation term_rel := (term_rel' val_rel).

Notation cnt_rel := (cnt_rel' val_rel).

Opaque val_rel.

Lemma res_rel_montone : 
  (forall k v1 v2, val_rel k v1 v2 -> val_rel (S k) v1 v2) -> 
    (forall k r1 r2, res_rel k r1 r2 -> res_rel (S k) r1 r2).
Proof.
  induction k, r1, r2; simpl; auto.
Qed.

Lemma eval_0_timeout : forall Γ Γc t io, 
  evalₜ 0 Γ Γc t io = (Rtimeout, io).
Proof.
  auto.
Qed.

Ltac apply_eval_0_timeout := 
  match goal with
  | H : evalₜ 0 _ _ _ _ = (_, _) |- _ =>
      rewrite eval_0_timeout in H; invert_constr
  end.

Opaque evalₜ.

Lemma term_rel_monotone : 
  (forall k v1 v2, val_rel k v1 v2 -> val_rel (S k) v1 v2) -> 
    (forall k e1 e2, term_rel k e1 e2 -> term_rel (S k) e1 e2).
Proof.
  induction k; destruct e1 as [[? ?] ?], e2 as [[? ?] ?]; destruct t, t0.
  all: simpl in *; intros.
  all: destruct k'; repeat apply_eval_0_timeout; try lia.
  all: repeat reduce; simpl_lia.
  all: pose proof (H0 A)
  eapply H0 in A.
  - unfold evalₜ in *. 

Lemma res_rel_refl_aux : 
  (forall k v, val_rel k v v) -> (forall k r, res_rel k r r).
Proof.
  intros; induction r; simpl; auto.
Qed.

Lemma term_rel_refl_aux : 
  (forall k v, val_rel k v v) -> (forall k e, term_rel k e e).
Proof.
  intros; induction k; destruct e as [[Γ Γc] t]; simpl; auto with lia.
  intros. exists k', r1; intuition auto.
  fold res_rel. auto using res_rel_refl_aux.
Qed.

Lemma eval_env_rel : 


Lemma cnt_rel_refl_aux : 
  (forall k v, val_rel k v v) -> (forall k cnt, cnt_rel k cnt cnt).
Proof.
  intros; destruct cnt; destruct cnt; repeat reduce.
  - (* Cnt0 *)
    exists k', r1; fold res_rel. intuition auto using res_rel_refl_aux.
  - exists k', r1; fold res_rel. intuition auto using res_rel_refl_aux.
  


Section value_rel.
  Variable term_rel : nat -> env value * env cntV * term -> env value * env cntV * term -> Prop.
  Variable cps_rel : nat -> cntV -> cntV -> Prop.
  
  Notation "e1 '≡ₜ' e2 '@' k" := (term_rel k e1 e2) (at level 70, no associativity).
  Notation "cnt1 '≡ᵧ' cnt2 '@' k" := (cps_rel k cnt1 cnt2) (at level 70, no associativity).

  Definition val_sub (v1 v2 : value) : Prop :=
    match v2 with
    | Tuple v2_1 v2_2 => v1 = v2_1 \/ v1 = v2_2
    | Left v2 => v1 = v2 
    | Right v2 => v1 = v2 
    | _ => False
    end.

  Definition arg_lt (a1 a2 : nat * value) := 
    match a1, a2 with
    | (k1, v1), (k2, v2) => k1 < k2 \/ val_sub v1 v2
    end.

  Require Import Program Program.Wf.

  Program Fixpoint val_rel' (a : nat * value) (v2 : value) { wf arg_lt a } : Prop := 
    let (k, v1) := a in 
    match v1, v2 with
    | Lit l1, Lit l2 => l1 = l2 
    | Tuple v1_1 v1_2, Tuple v2_1 v2_2 =>
        val_rel' (k, v1_1) v2_1 /\ val_rel' (k, v1_2) v2_2
    | Left v1, Left v2 =>
        val_rel' (k, v1) v2 
    | Right v1, Right v2 =>
        val_rel' (k, v1) v2
    | Fun (Fnt n1 c1 a1 b1) Γ1, Fun (Fnt n2 c2 a2 b2) Γ2 => 
        forall v1' v2' ac1 bc1 Γc1 Γcnt1 ac2 bc2 Γc2 Γcnt2, 
          let Γ1' := Γ1 + (n1, v1) + (a1, v1') in 
          let cnt1 := Cnt (Cnt1 c1 ac1 bc1) Γc1 Γcnt1 in
          let Γc1' := empty + (c1, cnt1) in 
          let Γ2' := Γ2 + (n2, v2) + (a2, v2') in 
          let cnt2 := Cnt (Cnt1 c2 ac2 bc2) Γc2 Γcnt2 in
          let Γc2' := empty + (c2, cnt2) in 
          val_rel' (k, v1') v2' ->
          cnt1 ≡ᵧ cnt2 @ k -> 
            (Γ1', Γc1', b1) ≡ₜ (Γ2', Γc2', b2) @ k
    | _, _ => False
    end.
  Obligation 1.
    
  Defined.
    
    Print val_rel'.

  Definition val_rel (k : nat) (v1 v2 : value) : Prop :=
    val_rel' (k, v1) v2.
  

  Function val_rel (k : nat) (v1 v2 : value) {struct k} : Prop := 
    match v1, v2 with 
    | Lit l1, Lit l2 => l1 = l2 
    | Tuple v1_1 v1_2, Tuple v2_1 v2_2 => 
        (* v1_1 ≡ᵥ v2_1 @ k /\ v1_2 ≡ᵥ v2_2 @ k *)
        val_rel k v1_1 v2_1 /\ val_rel k v1_2 v2_2
    | Left v1, Left v2 => 
        (* v1 ≡ᵥ v2 @ k *)
        val_rel k v1 v2
    | Right v1, Right v2 => 
        (* v1 ≡ᵥ v2 @ k *)
        val_rel k v1 v2
    | Fun (Fnt n1 c1 a1 b1) Γ1, Fun (Fnt n2 c2 a2 b2) Γ2 => 
        let f1 := Fnt n1 c1 a1 b1 in 
        let f2 := Fnt n2 c2 a2 b2 in
        forall v1' v2' ac1 bc1 Γc1 Γcnt1 ac2 bc2 Γc2 Γcnt2, 
          (* v1' ≡ᵥ v2' @ k ->  *)
          val_rel k v1' v2' ->
          let Γ1' := Γ1 + (n1, v1) + (a1, v1') in 
          let cnt1 := Cnt1 c1 ac1 bc1 in
          let Γc1 := empty + (c1, Cnt cnt1 Γc1 Γcnt1) in 
          let Γ2' := Γ2 + (n2, v2) + (a2, v2') in 
          let cnt2 := Cnt1 c2 ac2 bc2 in
          let Γc2 := empty + (c2, Cnt cnt2 Γc2 Γcnt2) in 
            (Γ1', Γc1, b1) ≡ₜ (Γ2', Γc2, b2) @ k
    | _, _ => False
    end.
  "v1 ≡ᵥ v2 @ k" := (val_rel k v1 v2). *)

  Inductive equiv_v : nat -> value -> value -> Prop := 
    | lit_rel : forall k l, Lit l ≡ᵥ Lit l @ k
    | equiv_tuple : forall k v1 v1' v2 v2', 
        v1 ≡ᵥ v2 @ k -> v1' ≡ᵥ v2' @ k -> Tuple v1 v1' ≡ᵥ Tuple v2 v2' @ k
    | equiv_left : forall k v1 v2, 
        v1 ≡ᵥ v2 @ k -> Left v1 ≡ᵥ Left v2 @ k
    | equiv_right : forall k v1 v2, 
        v1 ≡ᵥ v2 @ k -> Right v1 ≡ᵥ Right v2 @ k
    | equiv_fun : forall k n1 c1 a1 b1 Γ1 n2 c2 a2 b2 Γ2 ac bc Γc Γcnt,
        let f1 := Fnt n1 c1 a1 b1 in 
        let cnt1 := Cnt1 c1 ac bc in
        let Γ1' := Γ1 + (n1, Fun f1 Γ1) in 
        let Γc1 := empty + (c1, Cnt cnt1 Γc Γcnt) in 
        let f2 := Fnt n2 c2 a2 b2 in 
        let cnt2 := Cnt1 c2 ac bc in
        let Γ2' := Γ2 + (n2, Fun f2 Γ2) in 
        let Γc2 := empty + (c2, Cnt cnt2 Γc Γcnt) in 
        (forall v1 v2, v1 ≡ᵥ v2 @ k ->
        (* (forall k' v, k' < k -> )*)
          (Γ1' + (a1, v1), Γc1, b1) ≡ₜ (Γ2' + (a2, v2), Γc2, b2) @ k) ->
            Fun f1 Γ1 ≡ᵥ Fun f2 Γ2 @ S k
  where "v1 '≡ᵥ' v2 '@' k" := (equiv_v k v1 v2). *)

Section Equiv_env.
  Variable equiv_v : nat -> value -> value -> Prop.

  Definition equiv_env' (k m : nat) (e1 e2 : env value) : Prop :=
    forall k, m <= k -> forall v1, 
      e1 ? k = Some v1 -> exists v2, e2 ? k = Some v2 /\ equiv_v k v1 v2.
End Equiv_env.

Section Equiv_t.
  Variable equiv_v : nat -> value -> value -> Prop.

  Definition equiv_r' (k : nat) (r1 r2 : result) : Prop := 
    match r1, r2 with
    | Rtimeout, Rtimeout => True
    | Rerr, Rerr => True
    | Reoi, Reoi => True
    | Rhalt v1, Rhalt v2 => equiv_v k v1 v2
    | _, _ => False
    end.
  
  Definition equiv_t' (k : nat) (e1 e2 : env value * env cntV * term): Prop :=
    let '(Γ1, Γc1, t1) := e1 in 
    let '(Γ2, Γc2, t2) := e2 in 
      forall io r1 r2 io1 io2 f1 f2,  
        evalₜ k Γ1 Γc1 t1 io = (r1, io1, f1) -> 
        evalₜ k Γ2 Γc2 t2 io = (r2, io2, f2) ->
          f1 = f2 /\ equiv_r' f1 r1 r2 /\ io1 = io2.
End Equiv_t.

Section Equiv_c.
  Variable equiv_v : nat -> value -> value -> Prop.

  Definition equiv_c' (k : nat) (cnt1 cnt2 : cntV) : Prop :=
    match cnt1, cnt2 with
    | Cnt (Cnt0 n1 b1) Γ1 Γc1, Cnt (Cnt0 n2 b2) Γ2 Γc2 => 
        let Γc1' := Γc1 + (n1, cnt1) in 
        let Γc2' := Γc2 + (n2, cnt2) in 
        equiv_t' equiv_v k (Γ1, Γc1', b1) (Γ2, Γc2', b2)
    | Cnt (Cnt1 n1 a1 b1) Γ1 Γc1, Cnt (Cnt1 n2 a2 b2) Γ2 Γc2 => 
        forall v1 v2, equiv_v k v1 v2 -> 
          let Γ1' := Γ1 + (a1, v1) in 
          let Γc1' := Γc1 + (n1, cnt1) in 
          let Γ2' := Γ2 + (a2, v2) in 
          let Γc2' := Γc2 + (n2, cnt2) in 
            equiv_t' equiv_v k (Γ1', Γc1', b1) (Γ2', Γc2', b2)
    | _ , _ => False
    end.
End Equiv_c.

Require Import Program.Wf.

Program Fixpoint equiv_v (k : nat) (v1 v2 : value) {struct k}: Prop :=
  let fix equiv_v_aux (v1 v2 : value) {struct v1}: Prop :=
    match v1, v2 with
    | Lit l1, Lit l2 => l1 = l2
    | Tuple v1_1 v1_2, Tuple v2_1 v2_2 =>
        equiv_v_aux v1_1 v2_1 /\ equiv_v_aux v1_2 v2_2
    | Left v1, Left v2 =>
        equiv_v_aux v1 v2
    | Right v1, Right v2 =>
        equiv_v_aux v1 v2
    | Fun (Fnt n1 c1 a1 b1) Γ1, Fun (Fnt n2 c2 a2 b2) Γ2 =>
        match k with
        | 0 => True 
        | S k' => 
            forall v1' v2' ac1 bc1 Γc1 Γcnt1 ac2 bc2 Γc2 Γcnt2,
              let cnt1 := Cnt (Cnt1 c1 ac1 bc1) Γc1 Γcnt1 in
              let cnt2 := Cnt (Cnt1 c2 ac2 bc2) Γc2 Γcnt2 in
              let Γ1' := Γ1 + (n1, v1) + (a1, v1') in
              let Γ2' := Γ2 + (n2, v2) + (a2, v2') in
              let Γc1' := empty + (c1, cnt1) in
              let Γc2' := empty + (c2, cnt2) in
              equiv_v k' v1' v2' ->
              equiv_c' equiv_v k' cnt1 cnt2 -> 
                equiv_t' equiv_v k' (Γ1', Γc1', b1) (Γ2', Γc2', b2)
        end
    | _, _ => False
    end
  in equiv_v_aux v1 v2.

Notation equiv_r := (equiv_r' equiv_v).
Notation equiv_t := (equiv_t' equiv_v).
Notation equiv_c := (equiv_c' equiv_v).

Notation "r1 '≡ᵣ' r2" := (forall k, equiv_r k r1 r2) (at level 70, no associativity).
Notation "e1 '≡ₜ' e2" := (forall k, equiv_t k e1 e2) (at level 70, no associativity).
Notation "c1 '≡ᵧ' c2" := (forall k, equiv_c k c1 c2) (at level 70, no associativity).
Notation "v1 '≡ᵥ' v2" := (forall k, equiv_v k v1 v2) (at level 70, no associativity).

(* Lemma equiv_v_refl_0 : forall v, 
  equiv_v 0 v v.
Proof.
  induction v; reduce.
  destruct_match; reduce.
Qed.

Lemma equiv_r_refl_0 : forall r, 
  equiv_r 0 r r.
Proof.
  induction r; reduce.
  induction v; reduce.
  destruct_match; reduce.
Qed.

Lemma equiv_t_relf_0 : forall t Γ Γc,
  equiv_t 0 (Γ, Γc, t) (Γ, Γc, t).
Proof.
  induction t; reduce.
Qed.

Lemma equiv_c_refl_0 : forall c, 
  equiv_c 0 c c.
Proof.
  induction c; reduce.
  destruct_match; reduce.
Qed.

Lemma equiv_v_refl_1 : forall v, 
  equiv_v 1 v v.
Proof.
  induction v; reduce.
  destruct_match; reduce.
Qed.

Lemma equiv_r_refl_1 : forall r, 
  equiv_r 1 r r.
Proof.
  induction r; reduce.
  apply equiv_v_refl_1.
Qed.

Lemma equiv_t_relf_1 : forall t Γ Γc,
  equiv_t 1 (Γ, Γc, t) (Γ, Γc, t).
Proof.
  induction t; reduce.
  all: repeat destruct_match; reduce.
  apply equiv_v_refl_1.
Qed.

Lemma bin_op_equiv_v : forall op k v1 v2 e a1 a2 n v1',
  equiv_v k v1 v2 -> 
  binary_op_atom (e + (n, v1)) op a1 a2 = Some v1' -> 
    exists v2', binary_op_atom (e + (n, v2)) op a1 a2 = Some v2'.
Proof.
  destruct op, k, a1, a2; reduce; 
  unfold binary_op_atom, get_value_atom in *.
  all: repeat reduce || env || destruct_match; eauto.
Qed.

Lemma bin_op_equiv_v_err : forall op k v1 v2 e a1 a2 n, 
  equiv_v k v1 v2 -> 
  binary_op_atom (e + (n, v1)) op a1 a2 = None -> 
    binary_op_atom (e + (n, v2)) op a1 a2 = None.
Proof.
  destruct op, k, a1, a2; reduce;
  unfold binary_op_atom, get_value_atom in *.
  all: repeat reduce || env || destruct_match; eauto.
Qed.

Lemma un_op_equiv_v : forall op k v1 v2 e a n v1', 
  equiv_v k v1 v2 ->
  unary_op_atom (e + (n, v1)) op a = Some v1' -> 
    exists v2', unary_op_atom (e + (n, v2)) op a = Some v2'.
Proof.
  destruct op, k, a; reduce;
  unfold unary_op_atom, get_value_atom in *.
  all: repeat reduce || env || destruct_match; eauto.
Qed.

Lemma un_op_equiv_v_err : forall op k v1 v2 e a n,
  equiv_v k v1 v2 ->
  unary_op_atom (e + (n, v1)) op a = None -> 
    unary_op_atom (e + (n, v2)) op a = None.
Proof.
  destruct op, k, a; reduce;
  unfold unary_op_atom, get_value_atom in *.
  all: repeat reduce || env || destruct_match; eauto.
Qed.

Lemma equiv_c_refl_1 : forall c, 
  equiv_c 1 c c.
Proof.
  destruct c; reduce.
  repeat destruct_match; reduce; 
  try solve [
    unfold get_value_atom in *;
    repeat reduce || env || destruct_match
  ].
  - apply equiv_v_refl_1.
  - destruct (binary_op_atom (envV + (arg, v1)) op a1 a2) eqn:E.
    * pose proof (bin_op_equiv_v op 1 v1 v2 envV a1 a2 arg).
      apply (H2 v) in H as [v2' ?]; auto.
      rewrite H in *; reduce.
    * pose proof (bin_op_equiv_v_err op 1 v1 v2 envV a1 a2 arg).
      apply H2 in H; auto.
      rewrite H in *; reduce.
  - destruct (unary_op_atom (envV + (arg, v1)) op a) eqn:E.
    * pose proof (un_op_equiv_v op 1 v1 v2 envV a arg).
      apply (H2 v) in H as [v2' ?]; auto.
      rewrite H in *; reduce.
    * pose proof (un_op_equiv_v_err op 1 v1 v2 envV a arg).
      apply H2 in H; auto.
      rewrite H in *; reduce.
  - unfold get_value_atom in *;
    repeat reduce || env || destruct_match.
    apply equiv_v_refl_1.
Qed.

Lemma equiv_v_refl_2 : forall v, 
  equiv_v 2 v v.
Proof.
  induction v; reduce.
  destruct f; intros.
  destruct body.
  - destruct (binary_op_atom (e + (name, Fun (Fnt name retC arg (LetB name0 op a1 a2 body)) e) + (arg, v1')) op a1 a2) eqn:E.
    * pose proof (bin_op_equiv_v op 1 v1' v2' (e + (name, Fun (Fnt name retC arg (LetB name0 op a1 a2 body)) e)) a1 a2 arg).
      apply (H3 v) in H as [v' ?]; auto.
      rewrite H in *; reduce.
    * pose proof (bin_op_equiv_v_err op 1 v1' v2' (e + (name, Fun (Fnt name retC arg (LetB name0 op a1 a2 body)) e)) a1 a2 arg).
      apply H3 in H; auto.
      rewrite H in *; reduce.
  - destruct (unary_op_atom (e + (name, Fun (Fnt name retC arg (LetU name0 op a body)) e) + (arg, v1')) op a) eqn:E.
    * pose proof (un_op_equiv_v op 1 v1' v2' (e + (name, Fun (Fnt name retC arg (LetU name0 op a body)) e)) a arg).
      apply (H3 v) in H as [v' ?]; auto.
      rewrite H in *; reduce.
    * pose proof (un_op_equiv_v_err op 1 v1' v2' (e + (name, Fun (Fnt name retC arg (LetU name0 op a body)) e)) a arg).
      apply H3 in H; auto.
      rewrite H in *; reduce.
  - destruct cont; reduce.
  - destruct f; reduce.
  - destruct (IO.get_input io); reduce. 
    destruct p; reduce.
  - unfold get_value_atom in *.
    destruct a.
    * destruct (Nat.eq_dec n0 arg); subst.
      + rewrite lookup_add_eq in *.
        destruct v1', v2'; reduce.
        destruct l0; reduce.
        destruct f; reduce.
        destruct f; reduce.
      + rewrite lookup_add_ne in *; try lia.
        rewrite H1 in H2; reduce.
        apply equiv_r_refl_1.
    * rewrite H1 in H2; reduce.
      apply equiv_r_refl_1.
  - destruct (Nat.eq_dec retC name0); subst.
    * rewrite lookup_add_eq in *; reduce.
    * rewrite lookup_add_ne in *; try lia.
      rewrite lookup_empty in *; reduce.
  - destruct (Nat.eq_dec retC name0); subst.
    * rewrite lookup_add_eq in *.
      unfold get_value_atom in *.
      destruct a.



    * rewrite lookup_add_ne in *; try lia.
      rewrite lookup_empty in *; reduce.

    
    
    
    destruct_match; reduce.
  - unfold get_value_atom in *.
    destruct a.
    * destruct (Nat.eq_dec n0 arg); reduce.
      + rewrite lookup_add_eq in *.
        destruct v1', v2'; reduce.
        destruct l0; reduce.
        destruct f; reduce.
      + rewrite lookup_add_ne in *; try lia.
        destruct (Nat.eq_dec n0 name); reduce. {
          rewrite lookup_add_eq in *; reduce.
        } {
          rewrite lookup_add_ne in *; try lia.
          repeat reduce || destruct_match.
        }
    * destruct lit; reduce.
  - unfold get_value_atom in *.
    destruct a.
    * destruct (Nat.eq_dec n0 arg); reduce.
      + rewrite lookup_add_eq in *.
        destruct v1', v2'; reduce.
        destruct f; reduce.
      + rewrite lookup_add_ne in *; try lia.
        destruct (Nat.eq_dec n0 name); reduce.
    * destruct lit; reduce.
  - repeat reduce || env. 
  - repeat reduce || env. 
  - destruct (Nat.eq_dec retC name0); reduce.
    * rewrite lookup_add_eq in *.
      unfold get_value_atom in *.
      destruct a; reduce.

      env.
    
    repeat reduce || env. 


Lemma eval_equiv_env : forall k 

Lemma eval_equiv_v : forall k t Γ Γc io n v1 v2 r1 r2 io1 io2, equiv_v k v1 v2 ->
  evalₜ k (Γ + (n, v1)) Γc t io = (r1, io1) ->
  evalₜ k (Γ + (n, v2)) Γc t io = (r2, io2) ->
    equiv_r k r1 r2 /\ io1 = io2.
Proof.
  induction k, t; inversion 2; inversion 1; try solve [reduce].
  - destruct (Nat.eq_dec n name).
    * reduce.
      rewrite add_dup in H4.
    env.
  - reduce.  

Lemma equiv_v_refl_0 : forall v, equiv_v 0 v v.
Proof.
  induction v; repeat reduce || destruct_match.
Qed.

Lemma equiv_v_refl : forall k v, equiv_v k v v.
Proof. 
  induction v, k; auto using equiv_v_refl_0; reduce.
  destruct_match; reduce.
  - reduce.
  - reduce.
  - simpl. 
    apply (IHk v1).
    unfold equiv_v.
    repeat reduce || destruct_match.
  all: reduce. 
  - apply (IHv1 0).
  - apply (IHv2 0).
  - apply (IHv1 (S k)).
  - apply (IHv2 (S k)).
  - apply (IHv 0).
  - apply (IHv (S k)).
  - apply (IHv 0).
  - apply (IHv (S k)).
  - repeat reduce || destruct_match.
  - repeat reduce || destruct_match.

    admit.
Admitted.

Lemma value_eqb_equiv_v : forall v1 v2, value_eqb v1 v2 = true -> v1 ≡ᵥ v2.
Proof.
  induction v1; destruct v2; reduce.
  - destruct l, l0, k; reduce; f_equal.
    1, 2: apply BinInt.Z.eqb_eq in H; auto.
    all: apply Bool.eqb_prop in H; auto.
  - apply andb_prop in H. 
    destruct_and_H.
    pose proof (IHv1_1 _ H k).
    pose proof (IHv1_2 _ H0 k).
    destruct k; reduce.
  - pose proof (IHv1 _ H k).
    destruct k; reduce.
  - pose proof (IHv1 _ H k).
    destruct k; reduce.
Qed.

Lemma equiv_v_binary : forall k n v1 v2 env op a1 a2, equiv_v k v1 v2 -> 
  forall v1', binary_op_atom (env + (n, v1)) op a1 a2 = Some v1' ->
    exists v2', binary_op_atom (env + (n, v2)) op a1 a2 = Some v2' /\ equiv_v k v1' v2'.
Proof.
  induction v1, v2, k; reduce.
  - eexists; reduce; try eassumption. 
    apply (equiv_v_refl v1' 0).
  - eexists; reduce; try eassumption. 
    apply (equiv_v_refl v1' (S k)).
  - destruct_and_H.
    eapply IHv1_1 in H. 

  induction k, v1, v2; reduce.
  - destruct a1, a2; 
    unfold binary_op_atom, get_value_atom in *;
    repeat env || reduce || destruct_match || discriminate.
    all: exists v1'; reduce.
    all: apply (equiv_v_refl v1' 0).
  - destruct a1, a2, op; 
    unfold binary_op_atom, get_value_atom, compute_binary_op in *;
    repeat env || reduce || destruct_match || discriminate.
    all: eexists; repeat reduce. 
    all: try eapply (equiv_v_refl _ 0).
    all: f_equal.
    * 
      destruct v1_1, v1_2, v2_1, v2_2; reduce.
      all: repeat destruct_and_H || reduce || rewrite lit_eqb_refl.
    all: intuition eauto.
    all: exists v1'; reduce.

Lemma equiv_v_binary_err : forall k n v1 v2 env op a1 a2, equiv_v k v1 v2 -> 
  binary_op_atom (env + (n, v1)) op a1 a2 = None /\ 
  binary_op_atom (env + (n, v2)) op a1 a2 = None.


Lemma equiv_v_t_ind : forall k k' t envV envC n v1 v2 r1 r2 io io', k < k' -> 
  v1 ≡ᵥ v2 -> 
  evalₜ k (envV + (n, v1)) envC t io = (r1, io') ->
  evalₜ k (envV + (n, v2)) envC t io = (r2, io') -> 
    equiv_r (k - k') r1 r2.
Proof.
  induction k; reduce; try lia.
  destruct k'; simpl_lia.
  destruct t; reduce.
  - 
  

Opaque equiv_v.
Lemma equiv_r_refl : 
  (forall k v, equiv_v k v v) -> (forall k r, equiv_r k r r).
Proof.
  induction k, r; simpl; auto.
Qed.

Ltac destruct_eval := 
  match goal with
  | H : evalₜ ?f ?Γ ?Γc ?t ?io = (_,  _) |- _ =>
      let E := fresh "evalₜ" in 
      destruct (evalₜ f Γ Γc t io) eqn:E
  end.

Opaque minus.

Lemma equiv_t_relf : 
  (forall k v, equiv_v k v v) -> (forall k e, equiv_t k e e).
Proof.
  induction k, e; destruct p; induction t; simpl in *.
  all: intros; try lia.
  all: destruct_eval; repeat invert_constr; intuition auto using equiv_r_refl.
Qed.

Lemma equiv_c_refl: 
  (forall k v, equiv_v k v v) -> (forall k c, equiv_c k c c).
Proof.
  induction k, c; destruct cnt; simpl in *.
  all: intros; try lia.
  all: destruct_eval; repeat invert_constr; intuition auto using equiv_r_refl, equiv_t_relf.


Reserved Notation "v1 '≡ᵥ' v2 '@' k" (at level 70, no associativity).
Reserved Notation "r1 '≡ᵣ' r2 '@' k" (at level 70, no associativity).
Reserved Notation "e1 '≡ₜ' e2 '@' k" (at level 70, no associativity).  

Inductive equiv_v : nat -> value -> value -> Prop := 
  | equiv_lit : forall k l, Lit l ≡ᵥ Lit l @ k 
  | equiv_tuple : forall k v1 v1' v2 v2', 
      v1 ≡ᵥ v2 @ k -> v1' ≡ᵥ v2' @ k -> Tuple v1 v1' ≡ᵥ Tuple v2 v2' @ k
  | equiv_left : forall k v1 v2, 
      v1 ≡ᵥ v2 @ k -> Left v1 ≡ᵥ Left v2 @ k
  | equiv_right : forall k v1 v2, 
      v1 ≡ᵥ v2 @ k -> Right v1 ≡ᵥ Right v2 @ k
  | equiv_fun : forall k n1 c1 a1 b1 Γ1 n2 c2 a2 b2 Γ2 ac bc Γc Γcnt,
      let f1 := Fnt n1 c1 a1 b1 in 
      let cnt1 := Cnt1 c1 ac bc in
      let Γ1' := Γ1 + (n1, Fun f1 Γ1) in 
      let Γc1 := empty + (c1, Cnt cnt1 Γc Γcnt) in 
      let f2 := Fnt n2 c2 a2 b2 in 
      let cnt2 := Cnt1 c2 ac bc in
      let Γ2' := Γ2 + (n2, Fun f2 Γ2) in 
      let Γc2 := empty + (c2, Cnt cnt2 Γc Γcnt) in 
      (forall v1 v2, v1 ≡ᵥ v2 @ k ->
      (* (forall k' v, k' < k -> *)
        (Γ1' + (a1, v1), Γc1, b1) ≡ₜ (Γ2' + (a2, v2), Γc2, b2) @ k) ->
          Fun f1 Γ1 ≡ᵥ Fun f2 Γ2 @ S k
with equiv_r : nat -> result -> result -> Prop :=
  | equiv_halt : forall k v1 v2, 
      v1 ≡ᵥ v2 @ k -> Rhalt v1 ≡ᵣ Rhalt v2 @ k
  | equiv_err : forall k, Rerr ≡ᵣ Rerr @ k
  | equiv_eoi : forall k, Reoi ≡ᵣ Reoi @ k
  | equiv_timeout : forall k, Rtimeout ≡ᵣ Rtimeout @ k
with equiv_t : nat -> env value * env cntV * term -> env value * env cntV * term -> Prop := 
  | equiv_eval : forall k Γ1 Γ2 Γc1 Γc2 t1 t2,
      (forall k1 io io1 r1, k1 < k -> 
      evalₜ k1 Γ1 Γc1 t1 io = (r1, io1) -> 
        exists k2 io2 r2, 
          evalₜ k2 Γ2 Γc2 t2 io = (r2, io2) /\ io1 = io2 /\ r1 ≡ᵣ r2 @ (k1)) ->
            (Γ1, Γc1, t1) ≡ₜ (Γ2, Γc2, t2) @ k
where "v1 '≡ᵥ' v2 '@' k" := (equiv_v k v1 v2) and
      "r1 '≡ᵣ' r2 '@' k" := (equiv_r k r1 r2) and 
      "e1 '≡ₜ' e2 '@' k" := (equiv_t k e1 e2).

#[global]
Hint Constructors equiv_v equiv_r equiv_t : equiv_cps.

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
Hint Resolve equiv_v_trans equiv_r_trans : equiv_cps. *)

(* Lemma equiv_monotone : forall k  *)