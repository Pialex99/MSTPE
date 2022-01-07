From Utils Require Import Env Tactics.
From Common Require Import Literal Primitive.
From Src Require Import Tree Fun_sem.
From CPS Require Import Tree Fun_sem.
(* Equi. *)
Require Import FunInd.

Open Scope list_scope.

Module ST := Src.Tree.
Module SV := Src.Fun_sem.
Module CT := CPS.Tree.
Module CV := CPS.Fun_sem.

Function cps_rec (nf : nat) (t : ST.term) (cnt : nat) {struct t} : nat * CT.term :=
  match t with
  | ST.Var n => (nf, CT.AppC1 cnt (CT.Var n))
  | ST.Const l => (nf, CT.AppC1 cnt (CT.Lit l))
  | ST.Let n t r => 
      let (nf, cb) := cps_rec nf r cnt in
      let cn := nf in
      let (nf, t') := cps_rec (nf + 1) t cn in
      (nf, CT.LetC (CT.Cnt1 cn n cb) t')
  | ST.LetRec (ST.Fnt n a b) r => 
      let c := nf in 
      let (nf, b') := cps_rec (nf + 1) b c in 
      let (nf, r') := cps_rec nf r cnt in 
      (nf, CT.LetF (CT.Fnt n c a b') r')
  | ST.App f t =>
      let ct := nf in
      let ta := nf + 1 in 
      let af := nf + 2 in 
      let bt := CT.AppF (CT.Var af) cnt (CT.Var ta) in (* Once f and t have been computer, we call f *)
      let cntt := CT.Cnt1 ct ta bt in 
      let (nf, t') := cps_rec (nf + 3) t ct in
      let cf := nf in 
      let bf := CT.LetC cntt t' in (* Once we are done computing f, we compute t *)
      let cntf := CT.Cnt1 cf af bf in
      let (nf, f') := cps_rec (nf + 1) f cf in
      let res := CT.LetC cntf f' in 
      (nf, res)
  | ST.In => 
      let res := CT.LetIn nf (CT.AppC1 cnt (CT.Var nf)) in
      (nf + 1, res)
  | ST.Out t => 
      let c  := nf in 
      let a := nf + 1 in 
      let n := nf + 2 in 
      let b := CT.LetOut n (CT.Var a) (CT.AppC1 cnt (CT.Var n)) in
      let (nf, t') := cps_rec (nf + 3) t c in
      let res := CT.LetC (CT.Cnt1 c a b) t' in 
      (nf, res)
  | ST.Ite c t e => 
      let ct := nf in 
      let (nf, bt) := cps_rec (nf + 1) t cnt in 
      let cntt := CT.Cnt0 ct bt in
      let ce := nf in 
      let (nf, be) := cps_rec (nf + 1) e cnt in 
      let cnte := CT.Cnt0 ce be in
      let cc := nf in
      let ac := nf + 1 in
      let bc := CT.LetC cntt (CT.LetC cnte (CT.Ite (CT.Var ac) ct ce)) in 
      let cntc := CT.Cnt1 cc ac bc in
      let (nf, c') := cps_rec (nf + 2) c cc in 
      let res := CT.LetC cntc c' in 
      (nf, res)
  | ST.BinaryOp op t1 t2 =>
      let c2 := nf in 
      let a2 := nf + 1 in
      let a1 := nf + 2 in
      let n := nf + 3 in 
      let b2 := CT.LetB n op (CT.Var a1) (CT.Var a2) (CT.AppC1 cnt (CT.Var n)) in
      let cnt2 := CT.Cnt1 c2 a2 b2 in
      let (nf, t2') := cps_rec (nf + 4) t2 c2 in
      let c1 := nf in
      let b1 := CT.LetC cnt2 t2' in 
      let cnt1 := CT.Cnt1 c1 a1 b1 in (* When t1 is computed, we compute t2 *)
      let (nf, t1') := cps_rec (nf + 1) t1 c1 in
      let res := CT.LetC cnt1 t1' in
      (nf, res)
  | ST.UnaryOp op t => 
      let c := nf in
      let a := nf + 1 in 
      let n := nf + 2 in 
      let b := CT.LetU n op (CT.Var a) (CT.AppC1 cnt (CT.Var n)) in 
      let cntt := CT.Cnt1 c a b in
      let (nf, t') := cps_rec (nf + 3) t c in 
      let res := CT.LetC cntt t' in
      (nf, res)
  | ST.Match s (la, lt) (ra, rt) => 
      let cl := nf in 
      let (nf, lt') := cps_rec (nf + 1) lt cnt in
      let cntl := CT.Cnt1 cl la lt' in 
      let cr := nf in 
      let (nf, rt') := cps_rec (nf + 1) rt cnt in 
      let cntr := CT.Cnt1 cr ra rt' in
      let cs := nf in
      let sa := nf + 1 in
      let sb := CT.LetC cntl (CT.LetC cntr (CT.Match (CT.Var sa) cl cr)) in 
      let cnts := CT.Cnt1 cs sa sb in 
      let (nf, s') := cps_rec (nf + 2) s cs in 
      let res := CT.LetC cnts s' in 
      (nf, res)
  end.

Create HintDb cps.

Ltac cps_rec_nf_monotone_ind IH := 
  match goal with
  | H : cps_rec ?nf ?t ?c = (?nf', ?t') |- _ => 
         eapply IH in H; auto with lia
  end.

Lemma cps_rec_nf_monotone_size : forall n t cnt nf nf' t', ST.size t < n -> 
  cps_rec nf t cnt = (nf', t') -> nf <= nf'.
Proof with eauto with lia.
  induction n, t...
  all: repeat reduce || destruct_match || cps_rec_nf_monotone_ind IHn...
Qed.

Lemma cps_rec_nf_monotone : forall nf t cnt nf' t', 
  cps_rec nf t cnt = (nf', t') -> nf <= nf'.
Proof.
  eauto using cps_rec_nf_monotone_size.
Qed.

#[global]
Hint Resolve cps_rec_nf_monotone : cps.

Ltac cps_rec_nf_correct_ind IH := 
  match goal with
  | H : cps_rec ?nf ?t ?c = (?nf', ?t') |- _ => 
        pose proof (cps_rec_nf_monotone _ _ _ _ _ H);
        eapply IH in H; auto with lia; [idtac]
  end.

Opaque Nat.max.

Lemma cps_rec_nf_correct_size : forall n t cnt nf nf' t', ST.size t < n -> 
  ST.next_free t <= nf -> cnt < nf ->
  cps_rec nf t cnt = (nf', t') -> CT.next_free t' <= nf'.
Proof with auto with lia cps.
  induction n, t; repeat reduce || simpl_lia.
  all: try solve [
      repeat destruct_match; 
      repeat cps_rec_nf_correct_ind IHn || simpl_lia || invert_constr;
      unfold CT.next_free; fold CT.next_free; unfold CT.nf_atom;
      repeat apply max_le || split; auto with lia].
Qed.

Lemma cps_rec_nf_correct : forall nf t cnt nf' t', 
  ST.next_free t <= nf -> cnt < nf -> 
  cps_rec nf t cnt = (nf', t') -> CT.next_free t' <= nf'.
Proof.
  eauto using cps_rec_nf_correct_size.
Qed.

#[global]
Hint Resolve cps_rec_nf_correct : cps.

Definition cps nf t := 
  let c := nf in 
  let a := nf + 1 in
  let b := CT.Halt (CT.Var a) in 
  let cnt := CT.Cnt1 c a b in
  let (_, t') := cps_rec (nf + 2) t c in 
  CT.LetC cnt t'.

Fixpoint cpsᵥ (nf : nat) (v : SV.value) {struct v} : nat * CV.value :=
  match v with 
  | SV.Lit l => (nf, CV.Lit l)
  | SV.Tuple v1 v2 => 
      let (nf, v1') := cpsᵥ nf v1 in
      let (nf, v2') := cpsᵥ nf v2 in
      (nf, CV.Tuple v1' v2')
  | SV.Left v => 
      let (nf, v') := cpsᵥ nf v in
      (nf, CV.Left v')
  | SV.Right v => 
      let (nf, v') := cpsᵥ nf v in
      (nf, CV.Right v')
  | SV.Fun (ST.Fnt fname farg fbody) env => 
      let fix cps_rec_v_env nf env := 
        match env with
        | nil => (nf, nil)
        | (n, v) :: env => 
            let (nf, v') := cpsᵥ nf v in
            let (nf, env) := cps_rec_v_env nf env in
            (nf, (n, v') :: env)
        end in
      let (nf, env) := cps_rec_v_env nf env in
      let c := nf in
      let (nf, fbody) := cps_rec (nf + 1) fbody c in
      (nf, CV.Fun (CT.Fnt fname c farg fbody) env)
  end.

(* Definition equivᵥ v1 v2 := exists e, v1 = renameᵥ e v2.

Lemma cps_V_equiv' : forall v nf1 nf2, 
  let (nf1', v1) := cpsᵥ nf1 v in 
  let (nf2', v2) := cpsᵥ nf2 v in 
    exists e, (e = { } \/ (min e <= nf2 /\ nf2' < max e)) /\ v1 = renameᵥ e v2.
Proof.
  induction v; repeat reduce || destruct_match.
  - eexists; reduce.
  - pose proof (IHv1 nf1 nf2).
    pose proof (IHv2 n2 n1).
    repeat reduce || destruct_match || destruct_and_H || destruct_or_H.
    * eexists; reduce.
    * exists x.
      reduce. *)

Lemma cps_v_equiv : forall v nf1 nf2,
  let (_, v1) := cpsᵥ nf1 v in 
  let (_, v2) := cpsᵥ nf2 v in 
    equivᵥ nf1 v1 v2.
Proof.
  induction v; repeat reduce || destruct_match.
  - eexists; reduce.
  - pose proof (IHv1 nf1 nf2).
    pose proof (IHv2 n2 n1).
    repeat reduce || destruct_match.
    unfold equivᵥ in H, H0.
    repeat destruct_exist_H || destruct_and_H.
    repeat destruct_or_H; subst.
    * exists { }.
      repeat rewrite rename_v_empty in *.
      reduce.
    *  

    
    

Lemma cps_v_equiv : forall v nf1 nf2,
  let (_, v1) := cpsᵥ nf1 v in 
  let (_, v2) := cpsᵥ nf2 v in 
    v1 ≡ᵥ v2.
Proof with eauto with equiv_cps.
  induction v; repeat reduce || destruct_match...
  - (* Tuple *)
    specialize (IHv1 nf1 nf2).
    specialize (IHv2 nf1 nf2).
    repeat destruct_match || destruct_exist_H || reduce.

Fixpoint cps_envᵥ (nf : nat) (env : env SV.value) := 
  match env with 
  | nil => (nf, nil) 
  | (n, v)::env => 
      let (nf', v') := cpsᵥ nf v in 
      let (nf'', env') := cps_envᵥ nf' env in 
      (nf'', (n, v')::env')
  end.

Lemma cps_env_keep_elem : forall env nf1 nf2 n v,
  env ? n = Some v -> 
  let (_, env') := cps_envᵥ nf1 env in 
  let (_, v2) := cpsᵥ nf2 v in 
    exists v1 k, 
      env' ? n = Some v1 /\ v1 ≡ᵥ v2 @ k.
Proof. 
  induction env.
  - (* nil *) 
    repeat reduce.
  - destruct a; repeat reduce || destruct_match.
    + exists v.


Theorem cps_rec_correct : forall f f' t v io env io',
    evalₛ f env t io = (Rval v, io', f') -> forall nf c a b cenvV cenvC, 
    ST.next_free_env env <= nf -> ST.next_free t <= nf ->
    c < nf -> a < nf ->  CT.next_free b <= nf -> 
    CV.next_free_envV cenvV <= nf -> CV.next_free_envC cenvC <= nf -> 
      let cnt := Cnt (Cnt1 c a b) cenvV cenvC in
      let (nf', t') := cps_rec nf t c in 
      let (nf'', v') := cpsᵥ nf' v in 
      let (_, envV) := cps_envᵥ nf'' env in
      forall f1 envC,
        let (r1, io1) := evalₜ f1 envV (envC + (c, cnt)) t' io in 
        exists f2 k,
          let (r2, io2) := evalₜ f2 (envV + (a, v')) (envC + (c, cnt)) b io in 
            io1 = io2 /\ r1 ≡ᵣ r2 @ k.
Proof. 
  induction f, t; inversion 1; repeat reduce || destruct_match.
  - (* Var n *) 
    destruct f1 eqn:F; repeat reduce.
    + exists 0, 0; repeat reduce; auto with equiv_cps.
    + enough (c =? c = true).
      rewrite H in *.
      autorewrite*.
      
(* 
Theorem cps_rec_correct_timeout : forall f t io env io', 0 < f -> 
  evalₛ f env t io = (SV.Rtimeout, io') -> forall nf cnt ca cb envV envC, 
    ST.next_free t <= nf -> next_free_env env <= nf -> cnt < nf ->
    let (nf', env') := cps_envᵥ nf env in 
    let (_, t') := cps_rec nf' t cnt in 
    exists f', 0 < f' -> 
      evalₜ f' env' (empty + (cnt, Cnt (Cnt1 cnt ca cb) envV envC)) t' io = (Rtimeout, io').
Proof.
  induction f, t; try lia.
  all: repeat reduce || destruct_match || simpl_lia.
  - 
  all: eexists.


Theorem cps_correct_ind : forall t v io env f io',
  evalₛ f env t io = (Rval v, io') -> 
  ST.next_free t <= nf -> cnt < nf ->

Theorem cps_correct : forall t v io env f io',
  let nf := max (next_free t) (max (next_free_env env) (next_freeᵥ v)) in
  { io | env } t ~>(f) { Rval v, io' } ->
  exists v' f', snd (cpsᵥ nf v) ≡ᵥ v' /\
    { io | (snd (cps_envᵥ nf env), empty) } snd (cps nf t) ~>(f') { Rhalt v', io' }.
Proof.
  intros.
  induction H; simpl. *)