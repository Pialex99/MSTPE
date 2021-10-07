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

Set Implicit Arguments.


Section trc.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Inductive trc : A -> A -> Prop :=
  | TrcRefl : forall x, trc x x
  | TrcFront : forall x y z,
    R x y
    -> trc y z
    -> trc x z.

  Hint Constructors trc : core.

  Theorem trc_one : forall x y, R x y
    -> trc x y.
  Proof.
    eauto.
  Qed.

  Hint Resolve trc_one : core.

  Theorem trc_trans : forall x y, trc x y
    -> forall z, trc y z
      -> trc x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trans : core.

  Inductive trcEnd : A -> A -> Prop :=
  | TrcEndRefl : forall x, trcEnd x x
  | TrcBack : forall x y z,
    trcEnd x y
    -> R y z
    -> trcEnd x z.

  Hint Constructors trcEnd : core.

  Lemma TrcFront' : forall x y z,
    R x y
    -> trcEnd y z
    -> trcEnd x z.
  Proof.
    induction 2; eauto.
  Qed.

  Hint Resolve TrcFront' : core.

  Theorem trc_trcEnd : forall x y, trc x y
    -> trcEnd x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trcEnd : core.

  Lemma TrcBack' : forall x y z,
    trc x y
    -> R y z
    -> trc x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve TrcBack' : core.

  Theorem trcEnd_trans : forall x y, trcEnd x y
    -> forall z, trcEnd y z
      -> trcEnd x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trans : core.
  
  Theorem trcEnd_trc : forall x y, trcEnd x y
    -> trc x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trc : core.

  Inductive trcLiteral : A -> A -> Prop :=
  | TrcLiteralRefl : forall x, trcLiteral x x
  | TrcTrans : forall x y z, trcLiteral x y
    -> trcLiteral y z
    -> trcLiteral x z
  | TrcInclude : forall x y, R x y
    -> trcLiteral x y.

  Hint Constructors trcLiteral : core.

  Theorem trc_trcLiteral : forall x y, trc x y
    -> trcLiteral x y.
  Proof.
    induction 1; eauto.
  Qed.

  Theorem trcLiteral_trc : forall x y, trcLiteral x y
    -> trc x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trcLiteral trcLiteral_trc : core.

  Theorem trcEnd_trcLiteral : forall x y, trcEnd x y
    -> trcLiteral x y.
  Proof.
    induction 1; eauto.
  Qed.

  Theorem trcLiteral_trcEnd : forall x y, trcLiteral x y
    -> trcEnd x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trcLiteral trcLiteral_trcEnd : core.
End trc.

Notation "R ^*" := (trc R) (at level 0).
Notation "*^ R" := (trcEnd R) (at level 0).

#[global]
Hint Constructors trc : core.
