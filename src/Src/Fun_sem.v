From Frap Require Import Frap.
From Utils Require Import Stream Int Env Tactics.
From Src Require Import Tree.


Open Scope list_scope.

Inductive value :=
| Lit (l: literal)
| Tuple (v1 v2: value)
| Left (v: value)
| Right (v: value)
| Fun (f: function) (e: env value).

Fixpoint value_eqb (v1 v2 : value) :=
  match v1, v2 with 
  | Lit l1, Lit l2 => lit_eqb l1 l2
  | Tuple v1_1 v1_2, Tuple v2_1 v2_2 => value_eqb v1_1 v2_1 && value_eqb v1_2 v2_2
  | Left v1, Left v2 => value_eqb v1 v2
  | Right v1, Right v2 => value_eqb v1 v2
  | _, _ => false
  end.

Inductive result :=
| Rval (v: value) (* Intermediate result *)
| Rerr (* Type error *)
| Reoi (* End of Input *)
(* | Rhalt (n: int) (* End of program with Halt *) *)
| Rtimeout. (* Clock reached 0 *)

Definition is_val r := 
  match r with 
  | Rval _ => True 
  | _ => False 
  end.

(* Definition is_val_dec r : { True } + { False }. *)

Definition is_int_val r := 
  match r with 
  | Rval (Lit (IntLit _)) => True 
  | _ => False
  end.

Definition is_bool_val r := 
  match r with
  | Rval (Lit (BoolLit _)) => True 
  | _ => False
  end.

Definition is_either_val r := 
  match r with 
  | Rval (Left _) => True 
  | Rval (Right _) => True 
  | _ => False
  end.

Definition is_fun_val r := 
  match r with
  | Rval (Fun _ _) => True 
  | _ => False 
  end.

#[global]
Hint Unfold is_val is_int_val is_bool_val is_either_val is_fun_val : eval.

(* Record state := mk_state {env: env value; input: list int; output: list int}.

Definition next_input (s: state) := 
  match input s with
  | h :: t => Some (h, mk_state (env s) t (output s))
  | Nil => None 
  end.

Definition outputs (s: state) (o: int) := 
  mk_state (env s) (input s) (o :: output s).

Definition bind (s: state) (x: nat) (v: value) := 
  mk_state (Env.add (env s) x v) (input s) (output s). *)

Record IO := {input : list int; output : list int}.

Open Scope Z_scope.

Definition compute_binary_op op v1 v2 :=
  match op, v1, v2 with 
  | Add, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 + n2)))
  | Sub, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 - n2)))
  | Mul, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 * n2)))
  | Div, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 / n2)))
  | Mod, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 mod n2)))
  | Lt, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (BoolLit (n1 <? n2)))
  | Le, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (BoolLit (n1 <=? n2)))
  | Eq, v1, v2 => Rval (Lit (BoolLit (value_eqb v1 v2)))
  | Or, Lit (BoolLit b1), Lit (BoolLit b2) => Rval (Lit (BoolLit (b1 || b2)))
  | And, Lit (BoolLit b1), Lit (BoolLit b2) => Rval (Lit (BoolLit (b1 && b2)))
  | Tup, v1, v2 => Rval (Tuple v1 v2)
  | _, _, _ => Rerr
  end.

Definition compute_unary_op op v := 
  match op, v with 
  | Neg, Lit (IntLit n) => Rval (Lit (IntLit (-n)))
  | Not, Lit (BoolLit b) => Rval (Lit (BoolLit (negb b)))
  | Fst, Tuple v1 _ => Rval v1
  | Snd, Tuple _ v2 => Rval v2
  | Tree.Left, v => Rval (Left v)
  | Tree.Right, v => Rval (Right v)
  | _, _ => Rerr
  end.

Close Scope Z_scope.

Inductive eval : env value -> term -> IO -> nat -> result -> IO -> Prop :=
| eval_var : forall env n v io,
    lookup env n = Some v -> 
      eval env (Var n) io 1 (Rval v) io
| eval_var_err : forall env n io,
    lookup env n = None ->
      eval env (Var n) io 1 Rerr io
| eval_const : forall env l io,
      eval env (Const l) io 1 (Rval (Lit l)) io
| eval_let : forall env io n t v f io' t' f' r io'',
    eval env t io f (Rval v) io' ->
    eval (Env.add env n v) t' io' f' r io'' ->
      eval env (Let n t t') io (f + f' + 1) r io''
| eval_let_err : forall env io n t t' f r io',
    ~ (is_val r) -> 
    eval env t io f r io' ->
      eval env (Let n t t') io (f + 1) r io'
| eval_letrec : forall env io fname farg fbody f t io' r,
    eval (Env.add env fname (Fun (Func fname farg fbody) env)) t io f r io' ->
      eval env (LetRec (Func fname farg fbody) t) io (f + 1) r io'
| eval_app : forall env e1 e2 f1 f2 f3 io0 io1 io2 io3 fname farg fbody fenv v r,
    let f := (Fun (Func fname farg fbody) fenv) in
    eval env e1 io0 f1 (Rval f) io1 ->
    eval env e2 io1 f2 (Rval v) io2 ->
    eval (Env.add (Env.add fenv farg v) fname f) fbody io2 f3 r io3 ->
      eval env (App e1 e2) io0 (f1 + f2 + f3 + 1) r io3
| eval_app_err : forall env e1 e2 f io io' r,
    ~ (is_val r) ->
    eval env e1 io f r io' ->
      eval env (App e1 e2) io (f + 1) r io'
| evel_app_err' : forall env e1 e2 f io io' r,
    ~ (is_fun_val r) ->
    eval env e1 io f r io' ->
      eval env (App e1 e2) io (f + 1) Rerr io'
| evel_app_err'' : forall env e1 e2 f1 f2 fname farg fbody fenv io0 io1 io2 r,
    let f := (Fun (Func fname farg fbody) fenv) in
    ~ (is_val r) ->
    eval env e1 io0 f1 (Rval f) io1 ->
    eval env e2 io1 f2 r io2 ->
      eval env (App e1 e2) io0 (f1 + f2 + 1) r io2
| eval_in : forall env i is os,
      eval env In {|input := i::is; output := os|} 1 (Rval (Lit (IntLit i))) {|input := is; output := os|}
| eval_in_err : forall env os,
      eval env In {|input := nil; output := os|} 1 Reoi {|input := nil; output := os|}
| eval_out : forall env t f io is o os,
    eval env t io f (Rval (Lit (IntLit o))) {|input := is; output := os|} ->
      eval env (Out t) io (f + 1) (Rval (Lit UnitLit)) {|input := is; output := o::os|}
| eval_out_err : forall env t f io r io', 
    ~ (is_val r) -> 
    eval env t io f r io' ->
    eval env (Out t) io (f + 1) r io' 
| eval_out_err' : forall env t f io r io',
    ~ (is_int_val r) ->
    eval env t io f r io' ->
      eval env (Out t) io (f + 1) Rerr io'
| eval_ite_true : forall env cond thent elset f f' io io' r io'',
    eval env cond io f (Rval (Lit (BoolLit true))) io' ->
    eval env thent io' f' r io'' ->
      eval env (Ite cond thent elset) io (f + f' + 1) r io''
| eval_ite_false : forall env cond thent elset f f' io io' r io'',
    eval env cond io f (Rval (Lit (BoolLit false))) io' ->
    eval env elset io' f' r io'' ->
      eval env (Ite cond thent elset) io (f + f' + 1) r io''
| eval_ite_err : forall env cond thent elset f io r io',
    ~ (is_val r) ->
    eval env cond io f r io' ->
      eval env (Ite cond thent elset) io (f + 1) r io'
| eval_ite_err' : forall env cond thent elset f io r io',
    ~ (is_bool_val r) ->
    eval env cond io f r io' ->
      eval env (Ite cond thent elset) io (f + 1) Rerr io'
| eval_match_left : forall env scrut n lt rcase v f io io' f' r io'',
    eval env scrut io f (Rval (Left v)) io' ->
    eval (Env.add env n v) lt io' f' r io'' ->
      eval env (Match scrut (n, lt) rcase) io (f + f' + 1) r io'' 
| eval_match_right : forall env scrut n lcase rt v f io io' f' r io'',
    eval env scrut io f (Rval (Right v)) io' ->
    eval (Env.add env n v) rt io' f' r io'' ->
      eval env (Match scrut lcase (n, rt)) io (f + f' + 1) r io'' 
| eval_match_err : forall env scrut lcase rcase f r io io',
    ~ (is_val r) ->
    eval env scrut io f r io' ->
      eval env (Match scrut lcase rcase) io (f + 1) r io' 
| eval_match_err' : forall env scrut lcase rcase f r io io',
    ~ (is_either_val r) ->
    eval env scrut io f r io' ->
      eval env (Match scrut lcase rcase) io (f + 1) Rerr io' 
| eval_binop : forall env op t1 t2 v1 v2 f f' io io' io'',
    eval env t1 io f (Rval v1) io' ->
    eval env t2 io' f' (Rval v2) io'' ->
      eval env (BinaryOp op t1 t2) io (f + f' + 1) (compute_binary_op op v1 v2) io'' 
| eval_binop_err : forall env op t1 t2 r1 f io io',
    ~ (is_val r1) -> 
    eval env t1 io f r1 io' ->
      eval env (BinaryOp op t1 t2) io (f + 1) r1 io' 
| eval_binop_err' : forall env op t1 t2 r1 r2 f f' io io' io'',
    eval env t1 io f r1 io' ->
    ~ (is_val r2) -> 
    eval env t2 io' f' r2 io'' ->
      eval env (BinaryOp op t1 t2) io (f + f' + 1) r2 io''
| eval_unary : forall env op t v f io io',
    eval env t io f (Rval v) io' ->
      eval env (UnaryOp op t) io (f + 1) (compute_unary_op op v) io'
| eval_unary_err : forall env op t r f io io',
    ~ (is_val r) ->
    eval env t io f r io' ->
      eval env (UnaryOp op t) io (f + 1) r io'
| eval_timeout : forall env t io,
    eval env t io 0 Rtimeout io.

#[global]
Hint Constructors eval : eval.

Definition diverge t := forall env io f io',
  eval env t io f Rtimeout io'.
(* 
Lemma eval_timeout_monoton: forall t env io f io',
  eval env t io f Rtimeout io' -> forall f', f' <= f -> 
    exists io'', eval env t io f' Rtimeout io''.
Proof.
  inversion 1; subst.
  intros.
  invert H.
  - 
  induction 1.
  - destruct f'; intros; try lia; clear H0.
    eauto with eval.  *)

(* From Ltac2 Require Import Ltac2 Fresh.

Ltac2 destruct_fuel0 () :=
  match! goal with 
  | [|- context[eval _ _ _ ?f _ _]] => 
    let e := in_goal ident:(E) in 
    destruct constr:(f); eauto with eval;
    assert (e: S f = f + 1) by lia
  end.

Ltac2 notation destruct_fuel := destruct_fuel0 (). *)

Ltac destruct_fuel :=  
  match goal with 
  | [|- context[eval _ _ _ ?f _ _]] =>
    let e := fresh "E" in 
    destruct f; eauto with eval;
    assert (e: S f = f + 1) by lia;
    rewrite e in *; clear e
  end.

Ltac solve_eval_timeout_smaller :=
  match goal with
  | IH: forall _, _ < ?f -> exists _, eval _ _ _ _ _ _,
    l : ?f' < ?f |- _ => 
      specialize (IH _ l) as [? ?];
      eauto with eval
  | IH: forall _, _ < ?f1 -> exists _, eval _ _ _ _ _ _,
    _ :  ?f < ?f1 + ?f2 |- _ =>
      let l := fresh "l" in 
      let r := fresh "r" in
      destruct (lt_dec f f1) as [l | r]; [
      specialize (IH _ l) as [? ?];
      eauto with eval | idtac ]
  | IH: forall _, _ < ?f1 -> exists _, eval _ _ _ _ _ _,
    _ :  ?f < ?f1 + ?f2 + ?f3 |- _ =>
      let l := fresh "l" in 
      let r := fresh "r" in
      destruct (lt_dec f f1) as [l | r]; [
      specialize (IH _ l) as [? ?];
      eauto with eval | idtac ]
  end.

Lemma eval_timeout_smaller: forall t env io f v io',
  eval env t io f (Rval v) io' -> forall f', f' < f -> 
    exists io'', eval env t io f' Rtimeout io''.
Proof.
  induction 1; intros;
  destruct_fuel;
  repeat simpl_lia || solve_eval_timeout_smaller.
Qed.

Ltac instantiate_eval_timeout_smaller :=
  match goal with 
  | H: eval _ _ _ ?f (Rval ?v) _,
    A: _ < ?f |- _ => 
      pose proof eval_timeout_smaller _ _ _ _ _ _ H _ A as [? ?]
  end.
  
#[global]
Hint Resolve eval_timeout_smaller : eval.

(* Theorem eval_total: forall t env io, 
  (exists f io', eval env t io f Rerr io')
  \/ (exists f io', eval env t io f Reoi io')
  \/ (exists v f io', eval env t io f (Rval v) io')
  \/ (forall f, exists io', eval env t io f Rtimeout io').
Proof.
  induction t0; intros.
  - (* Var n *)
    destruct (lookup env n) eqn:E;
    intuition eauto with eval.
  - (* Const l *)
    intuition eauto with eval.
  - (* Let c t0_1 t0_2 *)
    specialize (IHt0_1 env io).
    repeat destruct_or_H || destruct_exist;
    intuition eauto with eval.
    + (* t0_1 reduces to value x0 *)
      specialize (IHt0_2 (Env.add env x x0) x2).
      repeat destruct_or_H || destruct_exist;
      intuition eauto with eval.
      (* t0_2 diverges *)
      repeat right.
      destruct f; eauto with eval.
      assert (A: S f = f + 1) by lia;
      rewrite A in *; clear A.
      destruct (lt_dec f x1); 
      try solve [
        instantiate_eval_timeout_smaller;
        eauto with eval
      ].
      simpl_lia.

      specialize (H0 f0) as [? ?].
      eauto with eval.
    + (* t0_1 diverges *)
      repeat right.
      intro.
      destruct_fuel.
      specialize (H f) as [? ?].
      eauto with eval.
  - (* LetRec f t0 *)
    destruct f.
    specialize (IHt0 (Env.add env fname (Fun (Func fname arg body) env)) io);
    repeat destruct_or_H || destruct_exist;
    intuition eauto with eval.
    
    repeat right.
    intros.
    destruct_fuel.
    specialize (H f) as [? ?];
    eauto with eval.
  - (* App t0_1 t0_2 *)
    admit.
  - (* In *)
    destruct io eqn:E.
    destruct input0 eqn:E';
    intuition eauto with eval.
  - (* Out *)
    specialize (IHt0 env io);
    repeat destruct_exist || destruct_or_H;
    intuition eauto with eval.
    + destruct x;
      try solve [
        left;
        exists (x0 + 1), x1;
        eapply eval_out_err';
        eauto; auto
      ].
      destruct l;
      try solve [
        left;
        exists (x0 + 1), x1;
        eapply eval_out_err';
        eauto; auto
      ].
      destruct x1 eqn:E.
      intuition eauto with eval.
    + repeat right; intros.
      destruct_fuel.
      specialize (H f) as [? ?].
      eauto with eval.
  -  

    intuition eauto with eval lia.
      

      specialize (H0 (f - x1)).
      reduce.
      destruct (lt_dec x1 f).
      * (* we have enough fuel to compute t0_1 *)
        assert (A: f = x1 + (f - x1 - 1) + 1). 
        lia.
      subst; rewrite A.
      exists x3.
      eapply (eval_let _ _ _ _ _ _ _ _ _ _ _).
      constructor; eauto.
      eauto with eval lia.
    
Qed. *)


