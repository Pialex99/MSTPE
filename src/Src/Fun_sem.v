Require Import Arith Bool List.
From Utils Require Import Stream Int Env Tactics IO.
From Src Require Import Tree.

Inductive value :=
| Lit (l: literal)
| Tuple (v1 v2: value)
| Left (v: value)
| Right (v: value)
| Fun (f: function) (e: env value).

#[global]
Hint Constructors value : eval.

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

Definition is_timeout r := 
  match r with
  | Rtimeout => True
  | _ => False
  end.

Definition is_val r := 
  match r with 
  | Rval _ => True 
  | _ => False 
  end.

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
Hint Unfold is_val is_int_val is_bool_val is_either_val is_fun_val is_timeout : eval.

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


Open Scope Z_scope.

Definition compute_binary_op op v1 v2 :=
  match op, v1, v2 with 
  | Add, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 + n2)))
  | Sub, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 - n2)))
  | Mul, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 * n2)))
  | Div, Lit (IntLit n1), Lit (IntLit 0) => Rerr
  | Div, Lit (IntLit n1), Lit (IntLit n2) => Rval (Lit (IntLit (n1 / n2)))
  | Mod, Lit (IntLit n1), Lit (IntLit 0) => Rerr
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
  | Primitive.Left, v => Rval (Left v)
  | Primitive.Right, v => Rval (Right v)
  | Id, v => Rval v
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
| eval_app_err' : forall env e1 e2 f io io' r,
    is_val r -> ~ (is_fun_val r) ->
    eval env e1 io f r io' ->
      eval env (App e1 e2) io (f + 1) Rerr io'
| eval_app_err'' : forall env e1 e2 f1 f2 fname farg fbody fenv io0 io1 io2 r,
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
    is_val r -> ~ (is_int_val r) -> 
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
    is_val r -> ~ (is_bool_val r) ->
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
    is_val r -> ~ (is_either_val r) ->
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
| eval_binop_err' : forall env op t1 t2 v1 r2 f f' io io' io'',
    eval env t1 io f (Rval v1) io' ->
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
    eval env t io 0 Rtimeout io
| eval_extra_fuel : forall env t f io io' r,
    ~ (is_timeout r) ->
    eval env t io f r io' ->
      eval env t io (f + 1) r io'.

#[global]
Hint Constructors eval : eval.

Definition diverge t := forall env io f io',
  eval env t io f Rtimeout io'.

Ltac destruct_fuel :=  
  match goal with 
  | [|- context[eval _ _ _ ?f _ _]] =>
    let e := fresh "E" in 
    destruct f; eauto with eval;
    assert (e: S f = f + 1) by lia;
    rewrite e in *; clear e
  end.

Ltac solve_eval_min_fuel :=
  match goal with
  | IH: forall _, _ < ?f -> exists _, eval _ _ _ _ _ _,
    l : _ < ?f |- _ => 
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

Ltac instantiate_eval_min_fuel_IH :=
  match goal with 
  | IH: ~ is_timeout _ -> exists f_min, eval _ _ _ f_min _ _ /\ _ |- _ =>
      let f_min := fresh "f_min" in 
      unshelve epose proof IH _ as [f_min [? ?]]; auto;
      clear IH
  end.

Ltac find_min_fuel :=
  match goal with 
  | IH1: forall _, _ < ?f_min1 -> _,
    IH2: forall _, _ < ?f_min2 -> _,
    IH3: forall _, _ < ?f_min3 -> _ |- _ =>
      (
        exists (f_min1 + f_min2 + f_min3 + 1); split; 
        [eauto with eval; fail | idtac]
      ) || (
        exists (f_min1 + f_min3 + f_min2 + 1); split; 
        [eauto with eval; fail | idtac]
      ) || (
        exists (f_min2 + f_min1 + f_min3 + 1); split; 
        [eauto with eval; fail | idtac]
      ) || (
        exists (f_min2 + f_min3 + f_min1 + 1); split; 
        [eauto with eval; fail | idtac]
      ) || (
        exists (f_min3 + f_min1 + f_min2 + 1); split; 
        [eauto with eval; fail | idtac]
      ) || (
        exists (f_min3 + f_min2 + f_min1 + 1); split; 
        [eauto with eval; fail | idtac]
      )
  | IH1: forall _, _ < ?f_min1 -> _,
    IH2: forall _, _ < ?f_min2 -> _ |- _ =>
      (
        exists (f_min1 + f_min2 + 1); split; 
        [eauto with eval; fail | idtac]
      ) || (
        exists (f_min2 + f_min1 + 1); split; 
        [eauto with eval; fail | idtac]
      )
  | IH: forall _, _ < ?f_min -> _ |- _ =>
      exists (f_min + 1); split; 
      eauto with eval
  | |- _ => 
      exists 1; split; eauto with eval
  end.

Lemma eval_min_fuel: forall t env io f r io',
  ~ (is_timeout r) -> 
  eval env t io f r io' -> 
  exists f_min, eval env t io f_min r io' /\
  (forall f', f' < f_min -> 
    exists io'', eval env t io f' Rtimeout io'').
Proof.
  intros t env io f r io' HR;
  induction 1;
  repeat instantiate_eval_min_fuel_IH;
  try solve [
    find_min_fuel; intros;
    destruct_fuel;
    repeat simpl_lia || solve_eval_min_fuel
  ]; try solve [
    destruct r; eauto with eval
  ].
  unfold is_timeout in HR; auto with exfalso.
Qed.

Ltac rewrite_S_fuel :=
  match goal with 
  | |- eval _ _ _ (S ?n) _ _ =>
      rewrite_S n
  end.

Lemma eval_min_fuel': forall f f' env t io r io',
  ~ (is_timeout r) ->
  eval env t io f r io' ->
    f <= f' -> eval env t io f' r io'.
Proof.
  induction 3; try rewrite_S_fuel; auto with eval.
Qed. 

Ltac instantiate_eval_min_fuel t :=
  match goal with 
  | H: eval _ t _ ?f (Rval _) _ |- _ => 
      let f_min := fresh "f_min" in
      let H_eval := fresh "H_eval" in 
      let H' := fresh "H" in
      unshelve epose proof eval_min_fuel _ _ _ _ _ _ _ H as [f_min [H_eval H']];
      auto with eval; clear H;
      let l := fresh "l" in 
      let r := fresh "r" in
      destruct (lt_dec f f_min) as [l | r];
      [
        let io := fresh "io" in    
        apply (H' _) in l as [io ?];
        exists Rtimeout, io; eauto with eval | repeat simpl_lia; clear H'
      ]
  end.
  
#[global]
Hint Resolve eval_min_fuel eval_min_fuel': eval.

Ltac solve_error_cases :=
  match goal with 
  | H: eval _ _ _ _ ?r ?io' |- _ =>
      exists r, io'; eauto with eval
  end.

Ltac instantiate_eval_total_ind_IH env t io f :=
  match goal with
  | IH: forall f' t env io, f' < _ -> exists r io', eval env t io f' r io' |- _ =>
      let r := fresh "r" in
      let io' := fresh "io" in
      unshelve epose proof IH f t env io _ as [r [io' ?]]; subst;
      eauto with eval lia; destruct r; try solve [solve_error_cases]
  end.

Lemma eval_total_ind: forall f f' t env io, f' < f -> exists r io',
  eval env t io f' r io'.
Proof.
  induction f; try lia; try simpl_lia.
  destruct t0; intros;
  destruct_fuel; simpl_lia.
  - (* Var n *)
    destruct (lookup env n) eqn:E;
    [exists (Rval v) | exists Rerr];
    eauto with eval lia.
  - (* Const l *) 
    exists (Rval (Lit l)); eauto with eval lia.
  - (* Let *) 
    instantiate_eval_total_ind_IH env t0_1 io f'.
    instantiate_eval_min_fuel t0_1.
    instantiate_eval_total_ind_IH (Env.add env x v) t0_2 io0 f'0.
  - (* LetRec *)  
    destruct f0 eqn:F.
    instantiate_eval_total_ind_IH (Env.add env fname (Fun f0 env)) t0 io f'.
  - (* App *) 
    instantiate_eval_total_ind_IH env t0_1 io f'.
    destruct v;
    try solve [
      (* Solve not function cases *)
      exists Rerr, io0;
      eapply eval_app_err'; eauto with eval; 
      autounfold with eval; auto
    ].
    destruct f0 eqn:F.
    instantiate_eval_min_fuel t0_1.
    instantiate_eval_total_ind_IH env t0_2 io0 f'0.
    instantiate_eval_min_fuel t0_2.
    instantiate_eval_total_ind_IH (Env.add (Env.add e arg v) fname (Fun (Func fname arg body) e)) body io1 f'1.
  - (* In *)  
    destruct io eqn:E.
    destruct input; 
    [exists Reoi | exists (Rval (Lit (IntLit z)))];
    eauto with eval lia.
  - (* Out *)  
    instantiate_eval_total_ind_IH env t0 io f'.
    destruct v;
    try solve [
      (* Solve not literal cases *)
      exists Rerr, io0;
      eapply eval_out_err'; eauto with eval;
      autounfold with eval; auto
    ].
    destruct l;
    try solve [
      (* Solve not integer literal cases *)
      exists Rerr, io0;
      eapply eval_out_err'; eauto with eval; 
      autounfold with eval; auto
    ].
    destruct io0.
    exists (Rval (Lit UnitLit));
    eauto with eval.
  - (* Ite *) 
    instantiate_eval_total_ind_IH env t0_1 io f'.
    destruct v;
    try solve [
      (* Solve not literal cases *)
      exists Rerr, io0;
      eapply eval_ite_err'; eauto with eval;
      autounfold with eval; auto
    ].
    destruct l;
    try solve [
      (* Solve not boolean literal cases *)
      exists Rerr, io0;
      eapply eval_ite_err'; eauto with eval;
      autounfold with eval; auto
    ].
    instantiate_eval_min_fuel t0_1.
    destruct b.
    + instantiate_eval_total_ind_IH env t0_2 io0 f'0.
    + instantiate_eval_total_ind_IH env t0_3 io0 f'0.
  - (* Binary primitives *)
    instantiate_eval_total_ind_IH env t0_1 io f'.
    instantiate_eval_min_fuel t0_1.
    instantiate_eval_total_ind_IH env t0_2 io0 f'0.
    eauto with eval.
  - (* Unary primitives *) 
    instantiate_eval_total_ind_IH env t0 io f'.
    eauto with eval.
  - (* Match *) 
    instantiate_eval_total_ind_IH env t0 io f'.
    destruct v;
    try solve [
      (* Solve not either cases *)
      exists Rerr, io0;
      eapply eval_match_err'; eauto with eval;
      autounfold with eval; auto
    ];
    instantiate_eval_min_fuel t0.
    + (* Left *)
      destruct lcase eqn:L.
      instantiate_eval_total_ind_IH (Env.add env n v) t1 io0 f'0.
    + (* Right *)
      destruct rcase eqn:R.
      instantiate_eval_total_ind_IH (Env.add env n v) t1 io0 f'0.
Qed.

Theorem eval_total: forall t env io f,
  exists r io', eval env t io f r io'.
Proof.
  eauto using eval_total_ind.
Qed.
