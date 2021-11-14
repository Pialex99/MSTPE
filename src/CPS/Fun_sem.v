Require Import Arith Bool List.
From Utils Require Import Stream Int Env Tactics IO.
From CPS Require Import Tree.

Inductive value :=
| Lit (l: literal)
| Tuple (v1 v2: value)
| Left (v: value)
| Right (v: value)
| Fun (f: fnt) (e: env value).

Fixpoint value_eqb (v1 v2 : value) :=
  match v1, v2 with 
  | Lit l1, Lit l2 => lit_eqb l1 l2
  | Tuple v1_1 v1_2, Tuple v2_1 v2_2 => value_eqb v1_1 v2_1 && value_eqb v1_2 v2_2
  | Left v1, Left v2 => value_eqb v1 v2
  | Right v1, Right v2 => value_eqb v1 v2
  | _, _ => false
  end.

Definition is_int_val v := 
  match v with
  | Lit (IntLit _) => True 
  | _ => False
  end.

Definition is_fun_val v := 
  match v with 
  | Fun _ _ => True
  | _ => False
  end.

Definition is_bool_val v := 
  match v with
  | Lit (BoolLit _) => True 
  | _ => False 
  end.

Inductive result :=
| Rhalt (v: value) (* End of program *)
| Rerr (* Type error *)
| Reoi (* End of Input *)
(* | Rhalt (n: int) (* End of program with Halt *) *)
| Rtimeout. (* Clock reached 0 *)

Open Scope Z_scope.

Definition compute_binary_op op v1 v2 :=
  match op, v1, v2 with 
  | Add, Lit (IntLit n1), Lit (IntLit n2) => Some (Lit (IntLit (n1 + n2)))
  | Sub, Lit (IntLit n1), Lit (IntLit n2) => Some (Lit (IntLit (n1 - n2)))
  | Mul, Lit (IntLit n1), Lit (IntLit n2) => Some (Lit (IntLit (n1 * n2)))
  | Div, Lit (IntLit n1), Lit (IntLit n2) => Some (Lit (IntLit (n1 / n2)))
  | Mod, Lit (IntLit n1), Lit (IntLit n2) => Some (Lit (IntLit (n1 mod n2)))
  | Lt, Lit (IntLit n1), Lit (IntLit n2) => Some (Lit (BoolLit (n1 <? n2)))
  | Le, Lit (IntLit n1), Lit (IntLit n2) => Some (Lit (BoolLit (n1 <=? n2)))
  | Eq, v1, v2 => Some (Lit (BoolLit (value_eqb v1 v2)))
  | Or, Lit (BoolLit b1), Lit (BoolLit b2) => Some (Lit (BoolLit (b1 || b2)))
  | And, Lit (BoolLit b1), Lit (BoolLit b2) => Some (Lit (BoolLit (b1 && b2)))
  | Tup, v1, v2 => Some (Tuple v1 v2)
  | _, _, _ => None
  end.

Definition compute_unary_op op v := 
  match op, v with 
  | Neg, Lit (IntLit n) => Some (Lit (IntLit (-n)))
  | Not, Lit (BoolLit b) => Some (Lit (BoolLit (negb b)))
  | Fst, Tuple v1 _ => Some v1
  | Snd, Tuple _ v2 => Some v2
  | Primitive.Left, v => Some (Left v)
  | Primitive.Right, v => Some (Right v)
  | Id, v => Some v
  | _, _ => None
  end.

Close Scope Z_scope.

Definition get_value_atom env a := 
  match a with 
  | Var n => lookup env n
  | Tree.Lit l => Some (Lit l)
  end.

Definition binary_op_atom env op a1 a2 := 
  let v1 := get_value_atom env a1 in
  let v2 := get_value_atom env a2 in 
    match v1, v2 with 
    | Some v1, Some v2 => compute_binary_op op v1 v2 
    | _, _ => None 
    end.

Definition unary_op_atom env op a := 
  let v := get_value_atom env a in 
    match v with 
    | Some v => compute_unary_op op v
    | _ => None 
    end.

Definition get_cnt0 (env : env (cnt * env value)) c := 
  match lookup env c with
  | Some (Cnt0 c' body, env') => if c =? c' then Some (Cnt0 c' body, env') else None 
  | _ => None
  end.

Definition get_cnt1 (env : env (cnt * env value)) c := 
  match lookup env c with
  | Some (Cnt1 c' arg body, env') => if c =? c' then Some (Cnt1 c' arg body, env') else None 
  | _ => None
  end.

Inductive eval : env value -> env (cnt * (env value)) -> term -> IO -> nat -> result -> IO -> Prop :=
| eval_letB : forall envV envC n op a1 a2 rest io f v r io',
    binary_op_atom envV op a1 a2 = Some v ->
    eval (Env.add envV n v) envC rest io f r io' ->
      eval envV envC (LetB n op a1 a2 rest) io (f + 1) r io'
| eval_letB_err : forall envV envC n op a1 a2 rest io,
    binary_op_atom envV op a1 a2 = None ->
      eval envV envC (LetB n op a1 a2 rest) io 1 Rerr io
| eval_letU : forall envV envC n op a rest io f v r io',
    unary_op_atom envV op a = Some v ->
    eval (Env.add envV n v) envC rest io f r io' ->
      eval envV envC (LetU n op a rest) io (f + 1) r io'
| eval_letU_err : forall envV envC n op a rest io,
    unary_op_atom envV op a = None ->
      eval envV envC (LetU n op a rest) io 1 Rerr io
| eval_letC0 : forall envV envC cname cbody rest io f r io',
    let cnt := Cnt0 cname cbody in 
    eval envV (Env.add envC cname (cnt, envV)) rest io f r io' ->
      eval envV envC (LetC cnt rest) io (f + 1) r io' 
| eval_letC1 : forall envV envC cname carg cbody rest io f r io',
    let cnt := Cnt1 cname carg cbody in 
    eval envV (Env.add envC cname (cnt, envV)) rest io f r io' ->
      eval envV envC (LetC cnt rest) io (f + 1) r io' 
| eval_letF : forall envV envC fname fretC farg fbody rest io f r io',
    let fnt := Fnt fname fretC farg fbody in
    eval (Env.add envV fname (Fun fnt envV)) envC rest io f r io' ->
      eval envV envC (LetF fnt rest) io (f + 1) r io' 
| eval_letIn : forall envV envC n rest i is os f r io',
    eval (Env.add envV n (Lit (IntLit i))) envC rest {|input:=is;output:=os|} f r io' ->
      eval envV envC (LetIn n rest) {|input:=i::is;output:=os|} (f + 1) r io'
| eval_letIn_err : forall envV envC n rest os,
    let io := {|input:=nil;output:=os|} in
      eval envV envC (LetIn n rest) io 1 Reoi io
| eval_letOut : forall envV envC n a rest is os f r io' o,
    get_value_atom envV a = Some (Lit (IntLit o)) -> 
    eval (Env.add envV n (Lit UnitLit)) envC rest {|input:=is;output:=o::os|} f r io' ->
      eval envV envC (LetOut n a rest) {|input:=is;output:=os|} (f + 1) r io'
| eval_letOut_err : forall envV envC n a rest io,
    get_value_atom envV a = None ->
      eval envV envC (LetOut n a rest) io 1 Rerr io
| eval_letOut_err' : forall envV envC n a rest io v,
    ~ (is_int_val v) ->
    get_value_atom envV a = Some v ->
      eval envV envC (LetOut n a rest) io 1 Rerr io
| eval_AppC0 : forall envV envC c cbody envV' io f r io',
    get_cnt0 envC c = Some (Cnt0 c cbody, envV') ->
    eval envV' empty cbody io f r io' ->
      eval envV envC (AppC0 c) io (f + 1) r io'
| eval_AppC0_err : forall envV envC c io,
    get_cnt0 envC c = None ->
      eval envV envC (AppC0 c) io 1 Rerr io
| eval_AppC1 : forall envV envC c a v cbody carg envV' io f r io',
    get_cnt1 envC c = Some (Cnt1 c carg cbody, envV') ->
    get_value_atom envV a = Some v ->
    eval (Env.add envV' carg v) empty cbody io f r io' ->
      eval envV envC (AppC1 c a) io (f + 1) r io'
| eval_AppC1_err : forall envV envC c a io,
    get_cnt1 envC c = None ->
      eval envV envC (AppC1 c a) io 1 Rerr io
| eval_AppC1_err' : forall envV envC c a cbody carg envV' io,
    get_cnt1 envC c = Some (Cnt1 c carg cbody, envV') ->
    get_value_atom envV a = None ->
      eval envV envC (AppC1 c a) io 1 Rerr io
| eval_AppF : forall envV envC af fname fretC farg fbody fenv c carg cbody cenv a v io f r io',
    let fnt := Fnt fname fretC farg fbody in
    let cnt := Cnt1 c carg cbody in
    get_value_atom envV af = Some (Fun fnt fenv) ->
    get_value_atom envV a = Some v ->
    get_cnt1 envC c = Some (cnt, cenv) ->
    eval (Env.add (Env.add fenv fname (Fun fnt fenv)) farg v) (Env.add empty fretC (cnt, cenv)) fbody io f r io' ->
      eval envV envC (AppF af c a) io (f + 1) r io'
| eval_AppF_err : forall envV envC af c a io,
    get_value_atom envV af = None ->
      eval envV envC (AppF af c a) io 1 Rerr io
| eval_AppF_err' : forall envV envC af c a io v,
    ~ (is_fun_val v) -> 
    get_value_atom envV af = Some v ->
      eval envV envC (AppF af c a) io 1 Rerr io
| eval_AppF_err'' : forall envV envC af c a io fname fretC farg fbody fenv,
    let fnt := Fnt fname fretC farg fbody in
    get_value_atom envV af = Some (Fun fnt fenv) ->
    get_value_atom envV a = None ->
      eval envV envC (AppF af c a) io 1 Rerr io
| eval_AppF_err''' : forall envV envC af c a io fname fretC farg fbody fenv v,
    let fnt := Fnt fname fretC farg fbody in
    get_value_atom envV af = Some (Fun fnt fenv) ->
    get_value_atom envV a = Some v ->
    get_cnt1 envC c = None ->
      eval envV envC (AppF af c a) io 1 Rerr io
| eval_Ite_true : forall envV envC c thenC elseC cbody cenv io f r io',
    let cnt := Cnt0 thenC cbody in 
    get_value_atom envV c = Some (Lit (BoolLit true)) ->
    get_cnt0 envC thenC = Some (cnt, cenv) ->
    eval cenv empty cbody io f r io' ->
      eval envV envC (Ite c thenC elseC) io (f + 1) r io'
| eval_Ite_true_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = Some (Lit (BoolLit true)) ->
    get_cnt0 envC thenC = None ->
      eval envV envC (Ite c thenC elseC) io 1 Rerr io
| eval_Ite_false : forall envV envC c thenC elseC cbody cenv io f r io',
    let cnt := Cnt0 elseC cbody in 
    get_value_atom envV c = Some (Lit (BoolLit false)) ->
    get_cnt0 envC elseC = Some (cnt, cenv) ->
    eval cenv empty cbody io f r io' ->
      eval envV envC (Ite c thenC elseC) io (f + 1) r io'
| eval_Ite_false_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = Some (Lit (BoolLit false)) ->
    get_cnt0 envC elseC = None ->
      eval envV envC (Ite c thenC elseC) io 1 Rerr io
| eval_Ite_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = None ->
      eval envV envC (Ite c thenC elseC) io 1 Rerr io
| eval_Ite_err' : forall envV envC c thenC elseC io v,
    ~ (is_bool_val v) ->
    get_value_atom envV c = Some v ->
      eval envV envC (Ite c thenC elseC) io 1 Rerr io
| eval_halt : forall envV envC a v io,
    get_value_atom envV a = Some v ->
      eval envV envC (Halt a) io 1 (Rhalt v) io
| eval_halt_err : forall envV envC a io,
    get_value_atom envV a = None ->
      eval envV envC (Halt a) io 1 Rerr io
| eval_timeout : forall envV envC t io,
      eval envV envC t io 0 Rtimeout io
| eval_extra_fuel : forall envV envC t io f r io',
    r <> Rtimeout ->
    eval envV envC t io f r io' ->
      eval envV envC t io (f + 1) r io'.

#[global]
Hint Constructors eval : eval.

Ltac destruct_fuel :=  
  match goal with 
  | [|- context[eval _ _ _ _ ?f _ _]] =>
    let e := fresh "E" in 
    destruct f; eauto with eval;
    assert (e: S f = f + 1) by lia;
    rewrite e in *; clear e
  end.

Ltac solve_error_cases :=
  match goal with 
  | |- _ => 
    exists 1; intuition eauto with eval;
    destruct_fuel; repeat simpl_lia
  end.

Ltac solve_induction_cases :=
  match goal with 
  | H : ?r <> Rtimeout,
    IH: ?r <> Rtimeout -> _ |- _ => 
      let f_min := fresh "f_min" in
      let H_eval := fresh "H_eval" in
      let H_timeout := fresh "H_timeout" in
      specialize (IH H) as [f_min [H_eval H_timeout]];
      exists (f_min + 1); intuition eauto with eval
  end.

Ltac solve_timeout_cases :=
  match goal with 
  | A : ?f < ?f_min,
    H_timeout : forall _, _ < ?f_min -> _ |- _ =>
      let io_final := fresh "io_final" in
      specialize (H_timeout _ A) as [io_final ?];
      eauto with eval
  end.

Lemma eval_min_fuel: forall t envV envC io f r io',
  r <> Rtimeout -> 
  eval envV envC t io f r io' -> 
  exists f_min, eval envV envC t io f_min r io' /\
  (forall f', f' < f_min -> 
    exists io'', eval envV envC t io f' Rtimeout io'').
Proof.
  induction 2; try solve [solve_error_cases];
  try solve [solve_induction_cases; 
    destruct_fuel; simpl_lia;
    solve_timeout_cases].
  - (* LetC0 *)
    solve_induction_cases.
    subst cnt; eauto with eval.
    destruct_fuel; simpl_lia.
    solve_timeout_cases.
    subst cnt; eauto with eval.
  - (* LetC1 *) 
    solve_induction_cases.
    subst cnt; eauto with eval.
    destruct_fuel; simpl_lia.
    solve_timeout_cases.
    subst cnt; eauto with eval.
  - (* LetF *) 
    solve_induction_cases.
    subst fnt; eauto with eval.
    destruct_fuel; simpl_lia.
    solve_timeout_cases.
    subst fnt; eauto with eval.
  - (* LetIn *) 
    subst io.
    exists 1.
    intuition eauto with eval.
    destruct_fuel; repeat simpl_lia.
  - auto.
Qed. 

Ltac rewrite_S_fuel :=
  match goal with 
  | |- eval _ _ _ _ (S ?n) _ _ =>
      rewrite_S n
  end.

Lemma eval_min_fuel': forall f f' envV envC t io r io',
  r <> Rtimeout ->
  eval envV envC t io f r io' ->
    f <= f' -> eval envV envC t io f' r io'.
Proof.
  induction 3; try rewrite_S_fuel; eauto with eval.
Qed.
  
#[global]
Hint Resolve eval_min_fuel eval_min_fuel': eval.

Ltac total_ind_solve_error_case :=
  match goal with 
  | |- context[eval _ _ _ ?io _ _ _] =>
    let H := fresh "H" in
    exists Rerr, io;
    apply (eval_min_fuel' 1); eauto with eval lia;
    intro H; discriminate H
  end.

Lemma eval_total_ind: forall f f' t envV envC io, f' < f -> exists r io',
  eval envV envC t io f' r io'.
Proof.
  induction f; try lia.
  destruct t0; intros;
  destruct_fuel; simpl_lia.
  - (* LetB *)
    destruct (binary_op_atom envV op a1 a2) eqn:E; try total_ind_solve_error_case.
    specialize (IHf _ t0 (Env.add envV name v) envC io A) as [r [io' ?]].
    eauto with eval.
  - (* LetU *) 
    destruct (unary_op_atom envV op a) eqn:E; try total_ind_solve_error_case.
    specialize (IHf _ t0 (Env.add envV name v) envC io A) as [r [io' ?]].
    eauto with eval.
  - (* LetC *) 
    destruct cont.
    + (* Cnt0 *)
      specialize (IHf _ t0 envV (Env.add envC name (Cnt0 name body, envV)) io A) as [r [io' ?]].
      eauto with eval.
    + (* Cnt1 *)
      specialize (IHf _ t0 envV (Env.add envC name (Cnt1 name arg body, envV)) io A) as [r [io' ?]].
      eauto with eval.
  - (* LetF *) 
    destruct f0.
    specialize (IHf _ t0 (Env.add envV name (Fun (Fnt name retC arg body) envV)) envC io A) as [r [io' ?]].
    eauto with eval.
  - (* LetIn *)
    destruct io.
    destruct input.
    + (* nil *) 
      exists Reoi, {|input:=nil;output:=output|}.
      apply (eval_min_fuel' 1); eauto with eval lia.
      intro; discriminate H.
    + (* z::input *) 
      specialize (IHf _ t0 (Env.add envV name (Lit (IntLit z))) envC {|input:=input;output:=output|} A) as [r [io' ?]].
      eauto with eval.
  - (* LetOut *) 
    destruct (get_value_atom envV a) eqn:E; try total_ind_solve_error_case.
    destruct v eqn:V;
    try solve [
      exists Rerr, io;
      apply (eval_min_fuel' 1); eauto with eval lia; [
      intro; discriminate H |
      eapply eval_letOut_err'; eauto;
      unfold is_int_val; auto]
    ].
    destruct l eqn:L;
    try solve [
      exists Rerr, io;
      apply (eval_min_fuel' 1); eauto with eval lia; [
      intro; discriminate H |
      eapply eval_letOut_err'; eauto;
      unfold is_int_val; auto]
    ].
    destruct io.
    specialize (IHf _ t0 (Env.add envV n (Lit UnitLit)) envC {|input:=input;output:=n0::output|} A) as [r [io' ?]].
    eauto with eval.
  - (* AppC0 *) 
    destruct (get_cnt0 envC name) eqn:C; try total_ind_solve_error_case.
    destruct p; destruct c eqn:cnt.
    + (* Cnt0 *) 
      assert (name = name0). {
        unfold get_cnt0 in C.
        repeat destruct_match; invert C.
        apply Nat.eqb_eq; auto.
      }
      subst.
      specialize (IHf _ body e empty io A) as [r [io' ?]].
      eauto with eval.
    + unfold get_cnt0 in C; repeat destruct_match;
      invert C.
  - (* AppC1 *) 
    destruct (get_cnt1 envC name) eqn:C; try total_ind_solve_error_case.
    destruct p; destruct c eqn:cnt; try solve [
    unfold get_cnt1 in C; repeat destruct_match; invert C].
    (* Cnt1 *) 
    assert (name = name0). {
      unfold get_cnt1 in C.
      repeat destruct_match; invert C.
      apply Nat.eqb_eq; auto.
    }
    subst.
    destruct (get_value_atom envV a) eqn:V; try total_ind_solve_error_case.
    specialize (IHf _ body (Env.add e arg v) empty io A) as [r [io' ?]].
    eauto with eval.
  - (* AppF *) 
    destruct (get_value_atom envV f0) eqn:F; try total_ind_solve_error_case.
    destruct v;
    try solve [
      exists Rerr, io;
      apply (eval_min_fuel' 1); eauto with eval lia; [
      intro; discriminate H |
      eapply eval_AppF_err'; eauto;
      unfold is_fun_val; auto]
    ].
    destruct f1.
    destruct (get_value_atom envV a) eqn:V; try total_ind_solve_error_case.
    destruct (get_cnt1 envC retC) eqn:C; try total_ind_solve_error_case.
    destruct p; destruct c; try solve [
    unfold get_cnt1 in C; repeat destruct_match; invert C].
    assert (retC = name0). {
      unfold get_cnt1 in C.
      repeat destruct_match; invert C.
      apply Nat.eqb_eq; auto.
    }
    subst.
    specialize (IHf _ body (Env.add (Env.add e name (Fun (Fnt name retC0 arg body) e)) arg v) (Env.add empty retC0 (Cnt1 name0 arg0 body0, e0)) io A) as [r [io' ?]].
    eauto with eval.
  - (* Ite *)
    destruct (get_value_atom envV c) eqn:V; try total_ind_solve_error_case.
    destruct v;
    try solve [
      exists Rerr, io;
      apply (eval_min_fuel' 1); eauto with eval lia; [
      intro; discriminate H |
      eapply eval_Ite_err'; eauto;
      unfold is_bool_val; auto]
    ].
    destruct l;
    try solve [
      exists Rerr, io;
      apply (eval_min_fuel' 1); eauto with eval lia; [
      intro; discriminate H |
      eapply eval_Ite_err'; eauto;
      unfold is_bool_val; auto]
    ].
    destruct b.
    + (* true *)
      destruct (get_cnt0 envC thenC) eqn:C; try total_ind_solve_error_case.
      destruct p; destruct c0; try solve [
      unfold get_cnt0 in C; repeat destruct_match; invert C]. 
      assert (thenC = name). {
        unfold get_cnt0 in C.
        repeat destruct_match; invert C.
        apply Nat.eqb_eq; auto.
      }
      subst.
      specialize (IHf _ body e empty io A) as [r [io' ?]].
      eauto with eval.
    + (* false *)
      destruct (get_cnt0 envC elseC) eqn:C; try total_ind_solve_error_case.
      destruct p; destruct c0; try solve [
      unfold get_cnt0 in C; repeat destruct_match; invert C]. 
      assert (elseC = name). {
        unfold get_cnt0 in C.
        repeat destruct_match; invert C.
        apply Nat.eqb_eq; auto.
      }
      subst.
      specialize (IHf _ body e empty io A) as [r [io' ?]].
      eauto with eval.
  - (* Halt *) 
    destruct (get_value_atom envV a) eqn:V; try total_ind_solve_error_case.
    exists (Rhalt v), io.
    eapply (eval_min_fuel' 1); eauto with eval lia.
    intro H; discriminate H.
Qed.
