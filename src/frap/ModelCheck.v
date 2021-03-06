(* 
  Copyright (c) 2016-2020, Adam Chlipala
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:

  - Redistributions of source code must retain the above copyright notice,
    this list of conditions and the following disclaimer.
  - Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.
  - The names of contributors may not be used to endorse or promote products
    derived from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
  ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.
*)

Require Import Classical.
From Frap Require Import Invariant Relations Sets.

Set Implicit Arguments.


Definition oneStepClosure_current {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st, invariant1 st
             -> invariant2 st.

Definition oneStepClosure_new {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st st', invariant1 st
                 -> sys.(Step) st st'
                 -> invariant2 st'.

Definition oneStepClosure {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  oneStepClosure_current sys invariant1 invariant2
  /\ oneStepClosure_new sys invariant1 invariant2.

Theorem prove_oneStepClosure : forall state (sys : trsys state) (inv1 inv2 : state -> Prop),
  (forall st, inv1 st -> inv2 st)
  -> (forall st st', inv1 st -> sys.(Step) st st' -> inv2 st')
  -> oneStepClosure sys inv1 inv2.
Proof.
  unfold oneStepClosure; tauto.
Qed.

Inductive multiStepClosure {state} (sys : trsys state)
  : (state -> Prop) -> (state -> Prop) -> (state -> Prop) -> Prop :=
| MscDone : forall inv,
    multiStepClosure sys inv (constant nil) inv
| MscStep : forall inv worklist inv' inv'',
    oneStepClosure sys worklist inv'
    -> multiStepClosure sys (inv \cup inv') (inv' \setminus inv) inv''
    -> multiStepClosure sys inv worklist inv''.

Lemma adding_irrelevant : forall A (s : A) inv inv',
    s \in (inv \cup inv') \setminus (inv' \setminus inv)
   -> s \in inv.
Proof.
  sets idtac.
  destruct (classic (inv s)); tauto.
Qed.

Lemma multiStepClosure_ok' : forall state (sys : trsys state) (inv worklist inv' : state -> Prop),
  multiStepClosure sys inv worklist inv'
  -> (forall st, sys.(Initial) st -> inv st)
  -> worklist \subseteq inv
  -> (forall s, s \in inv \setminus worklist
                      -> forall s', sys.(Step) s s'
                                    -> s' \in inv)
  -> invariantFor sys inv'.
Proof.
  induction 1; simpl; intuition.

  apply invariant_induction; simpl; intuition.
  eapply H1.
  red.
  unfold minus.
  split; eauto.
  assumption.
  
  apply IHmultiStepClosure; clear IHmultiStepClosure.
  intuition.
  apply H1 in H4.
  sets idtac.
  sets idtac.
  intuition.
  apply adding_irrelevant in H4.
  destruct (classic (s \in worklist)).
  destruct H.
  red in H7.
  eapply H7 in H6.
  right; eassumption.
  assumption.
  left.
  eapply H3.
  2: eassumption.
  sets idtac.
Qed.

Theorem multiStepClosure_ok : forall state (sys : trsys state) (inv : state -> Prop),
  multiStepClosure sys sys.(Initial) sys.(Initial) inv
  -> invariantFor sys inv.
Proof.
  intros; eapply multiStepClosure_ok'; eauto; sets idtac.
Qed.

Theorem oneStepClosure_empty : forall state (sys : trsys state),
  oneStepClosure sys (constant nil) (constant nil).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; intuition.
Qed.

Theorem oneStepClosure_split : forall state (sys : trsys state) st sts (inv1 inv2 : state -> Prop),
  (forall st', sys.(Step) st st' -> inv1 st')
  -> oneStepClosure sys (constant sts) inv2
  -> oneStepClosure sys (constant (st :: sts)) (constant (st :: nil) \cup inv1 \cup inv2).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; intuition.

  inversion H0; subst.
  unfold union; simpl; tauto.

  unfold union; simpl; eauto.

  unfold union in *; simpl in *.
  intuition (subst; eauto).
Qed.

Theorem singleton_in : forall {A} (x : A) rest,
  (constant (x :: nil) \cup rest) x.
Proof.
  unfold union; simpl; auto.
Qed.

Theorem singleton_in_other : forall {A} (x : A) (s1 s2 : set A),
  s2 x
  -> (s1 \cup s2) x.
Proof.
  unfold union; simpl; auto.
Qed.


(** * Abstraction *)

Inductive simulates state1 state2 (R : state1 -> state2 -> Prop)
  (sys1 : trsys state1) (sys2 : trsys state2) : Prop :=
| Simulates :
  (forall st1, sys1.(Initial) st1
               -> exists st2, R st1 st2
                              /\ sys2.(Initial) st2)
  -> (forall st1 st2, R st1 st2
                      -> forall st1', sys1.(Step) st1 st1'
                                      -> exists st2', R st1' st2'
                                                      /\ sys2.(Step) st2 st2')
  -> simulates R sys1 sys2.

Inductive invariantViaSimulation state1 state2 (R : state1 -> state2 -> Prop)
  (inv2 : state2 -> Prop)
  : state1 -> Prop :=
| InvariantViaSimulation : forall st1 st2, R st1 st2
  -> inv2 st2
  -> invariantViaSimulation R inv2 st1.

Lemma invariant_simulates' : forall state1 state2 (R : state1 -> state2 -> Prop)
  (sys1 : trsys state1) (sys2 : trsys state2),
  (forall st1 st2, R st1 st2
                   -> forall st1', sys1.(Step) st1 st1'
                                   ->  exists st2', R st1' st2'
                                                    /\ sys2.(Step) st2 st2')
  -> forall st1 st1', sys1.(Step)^* st1 st1'
                      -> forall st2, R st1 st2
                                     -> exists st2', R st1' st2'
                                                     /\ sys2.(Step)^* st2 st2'.
Proof.
  induction 2; simpl; intuition eauto.

  eapply H in H2.
  firstorder.
  apply IHtrc in H2.
  firstorder; eauto.
  eauto.
Qed.

Local Hint Constructors invariantViaSimulation : core.

Theorem invariant_simulates : forall state1 state2 (R : state1 -> state2 -> Prop)
  (sys1 : trsys state1) (sys2 : trsys state2) (inv2 : state2 -> Prop),
  simulates R sys1 sys2
  -> invariantFor sys2 inv2
  -> invariantFor sys1 (invariantViaSimulation R inv2).
Proof.
  inversion_clear 1; intros.
  unfold invariantFor; intros.
  apply H0 in H2.
  firstorder.
  apply invariant_simulates' with (sys2 := sys2) (R := R) (st2 := x) in H3; auto.
  firstorder; eauto.
Qed.
