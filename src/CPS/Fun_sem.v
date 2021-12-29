Require Import Arith Bool List.
From Utils Require Import Int Env Tactics IO.
From CPS Require Import Tree.
Require Import FunInd Recdef.

(* Declare Scope cps_scope.
Open Scope cps_scope. *)

Inductive value :=
| Lit (l: literal)
| Tuple (v1 v2: value)
| Left (v: value)
| Right (v: value)
| Fun (f: fnt) (e: env value).

Inductive cntV := Cnt (cnt : cnt) (envV : env value) (envC : env cntV).

Section Renameₑ.
  Variable rename_v : value -> value.
  Variable e : env nat.

  Fixpoint rename_e (env: env value) := 
    match env with 
    | nil => nil 
    | (n, v) :: env => 
        let n := get_or_id e n in
        let v := rename_v v in 
        let env := rename_e env in 
          (n, v) :: env
    end.
End Renameₑ.

Section Renameᵥ.
  Variable e : env nat.

  Fixpoint renameᵥ (v : value) := 
    match v with
    | Lit _ => v
    | Tuple v1 v2 => Tuple (renameᵥ v1) (renameᵥ v2)
    | Left v => Left (renameᵥ v)
    | Right v => Right (renameᵥ v)
    | Fun (Fnt n c a b) Γ => 
        let n := get_or_id e n in
        let c := get_or_id e c in
        let a := get_or_id e a in
        let b := renameₜ e b in
        let Γ := rename_e renameᵥ e Γ in 
          Fun (Fnt n c a b) Γ
    end.
End Renameᵥ.

Definition renameₑ (e : env nat) := rename_e (renameᵥ e) e.

Section Size_env.
  Variable size_v : value -> nat.
  
  Fixpoint size_e (e : env value) := 
    match e with
    | nil => 1
    | (n, v) :: e =>
        size_v v + size_e e 
    end.
End Size_env.

Fixpoint sizeᵥ v := 
  match v with
  | Lit _ => 1 
  | Tuple v1 v2 => 1 + sizeᵥ v1 + sizeᵥ v2 
  | Left v => 1 + sizeᵥ v 
  | Right v => 1 + sizeᵥ v 
  | Fun (Fnt _ _ _ b) Γ =>
      size b + size_e sizeᵥ Γ
  end.

Definition sizeₑ e := size_e sizeᵥ e.

Lemma size_v_gt_1 : forall v, 0 < sizeᵥ v.
Proof.
  induction v; reduce; try lia.
  destruct_match.
  pose proof (size_t_gt_1 body).
  lia.
Qed.

Lemma size_e_gt_1 : forall e, 0 < sizeₑ e.
Proof.
  induction e; reduce.
  destruct_match.
  pose proof (size_v_gt_1 v).
  lia.
Qed.

Lemma rename_e_v_empty_ind : forall n e v, 
  (sizeₑ e < n -> renameₑ { } e = e) /\
  (sizeᵥ v < n -> renameᵥ { } v = v).
Proof. 
  induction n; try lia; reduce.
  - destruct e; reduce.
    destruct_match; reduce.
    rewrite get_or_id_empty.
    pose proof (IHn e v0) as [IHe IHv].
    pose proof (size_v_gt_1 v0).
    pose proof (size_e_gt_1 e).
    unfold sizeₑ in H1.
    rewrite IHe, IHv; auto with lia.
    unfold sizeₑ; lia.
  - destruct v; reduce.
    2, 3: pose proof (IHn e v) as [_ ?];rewrite H0; auto with lia.
    * pose proof (IHn e v1) as [_ ?].
      pose proof (IHn e v2) as [_ ?].
      rewrite H0, H1; auto with lia.
    * destruct_match.
      rewrite 3 get_or_id_empty, rename_t_empty.
      pose proof (size_t_gt_1 body).
      pose proof (IHn e0 (Fun f e0)) as [? _].
      unfold sizeₑ, renameₑ in *.
      rewrite H1; auto with lia.
Qed.

Lemma rename_e_empty : forall e, renameₑ { } e = e.
Proof.
  intros.
  pose proof (rename_e_v_empty_ind (S (sizeₑ e)) e (Lit UnitLit)) as [? _].
  auto.
Qed.

Lemma rename_v_empty : forall v, renameᵥ { } v = v.
Proof.
  intros.
  pose proof (rename_e_v_empty_ind (S (sizeᵥ v)) { }) as [_ ?].
  auto.
Qed.

Fixpoint value_eqb (v1 v2 : value) :=
  match v1, v2 with 
  | Lit l1, Lit l2 => lit_eqb l1 l2
  | Tuple v1_1 v1_2, Tuple v2_1 v2_2 => value_eqb v1_1 v2_1 && value_eqb v1_2 v2_2
  | Left v1, Left v2 => value_eqb v1 v2
  | Right v1, Right v2 => value_eqb v1 v2
  | _, _ => false
  end.

Fixpoint has_no_fun_val v := 
  match v with 
  | Fun _ _ => False
  | Lit _ => True
  | Left v => has_no_fun_val v
  | Right v => has_no_fun_val v 
  | Tuple v1 v2 => has_no_fun_val v1 /\ has_no_fun_val v2
  end.

Lemma value_eqb_refl : forall v, has_no_fun_val v -> value_eqb v v = true.
Proof.
  induction v; reduce; intuition auto using lit_eqb_refl with bool.
Qed.

(* Fixpoint next_free_envV env :=
  match env with
  | nil => 0 
  | (n, v) :: env =>
      Nat.max (S n) (Nat.max (next_freeᵥ v) (next_free_envV env))
  end
with next_freeᵥ v := 
match v with 
| Lit _ => 0
| Tuple v1 v2 => Nat.max (next_freeᵥ v1) (next_freeᵥ v2)
| Left v => next_freeᵥ v
| Right v => next_freeᵥ v
| Fun (Fnt n c a b) e => 
    Nat.max (S n) (Nat.max (S c) (Nat.max (S a) (Nat.max (next_free b) (next_free_envV e))))
  end. *)

(* Fixpoint next_freeᵥ v := 
  match v with 
  | Lit _ => 0
  | Tuple v1 v2 => Nat.max (next_freeᵥ v1) (next_freeᵥ v2)
  | Left v => next_freeᵥ v
  | Right v => next_freeᵥ v
  | Fun (Fnt n c a b) e => 
      Nat.max (S n) (Nat.max (S c) (Nat.max (S a) (Nat.max (next_free b) (next_free_envV e))))
  end
with next_free_envV env :=
  match env with
  | nil => 0 
  | (n, v) :: env =>
      Nat.max (S n) (Nat.max (next_freeᵥ v) (next_free_envV env))
  end. *)

Section NFᵥ.
  Variable nf_v : value -> nat.

  Fixpoint nf_envV env :=
    match env with
    | nil => 0 
    | (n, v) :: env =>
        Nat.max (S n) (Nat.max (nf_v v) (nf_envV env))
    end.
End NFᵥ.
  
Fixpoint next_freeᵥ v := 
  match v with
  | Lit _ => 0
  | Tuple v1 v2 => Nat.max (next_freeᵥ v1) (next_freeᵥ v2)
  | Left v => next_freeᵥ v 
  | Right v => next_freeᵥ v 
  | Fun (Fnt n c a b) e => 
      Nat.max (S n) (Nat.max (S c) (Nat.max (S a) (Nat.max (next_free b) (nf_envV next_freeᵥ e))))
  end.

Definition next_free_envV := nf_envV next_freeᵥ.

Section NF_cnt.
  Variable nf_cnt : cntV -> nat.

  Fixpoint nf_envC env :=
    match env with
    | nil => 0 
    | (n, c) :: env => 
        Nat.max (S n) (Nat.max (nf_cnt c) (nf_envC env))
    end.
End NF_cnt.

Fixpoint next_free_cnt cnt := 
  match cnt with 
  | Cnt (Cnt0 c b) envV envC => 
      Nat.max (S c) (Nat.max (next_free b) 
        (Nat.max (next_free_envV envV) (nf_envC next_free_cnt envC)))
  | Cnt (Cnt1 c a b) envV envC => 
      Nat.max (S c) (Nat.max (S a) (Nat.max (next_free b) 
        (Nat.max (next_free_envV envV) (nf_envC next_free_cnt envC))))
  end.
  
Definition next_free_envC := nf_envC next_free_cnt.

(* Fixpoint next_freeᵥ v := 
  match v with
  | Lit _ => 0
  | Tuple v1 v2 => Nat.max (next_freeᵥ v1) (next_freeᵥ v2)
  | Left v => next_freeᵥ v 
  | Right v => next_freeᵥ v 
  | Fun (Fnt n c a b) e => 
      let fix next_free_env env := 
        match env with
        | nil => 0 
        | (n, v) :: env => 
            Nat.max (S n) (Nat.max (next_freeᵥ v) (next_free_env env))
        end in 
      Nat.max (S n) (Nat.max (S c) (Nat.max (S a) (Nat.max (next_free b) (next_free_env e))))
  end.

Fixpoint next_free_envV env :=
  match env with
  | nil => 0 
  | (n, v) :: env =>
      Nat.max (S n) (Nat.max (next_freeᵥ v) (next_free_envV env))
  end.

Fixpoint next_free_cnt cnt := 
  let fix next_free_cnt_envC env :=
    match env with
    | nil => 0 
    | (n, c) :: env => 
        Nat.max (S n) (Nat.max (next_free_cnt c) (next_free_cnt_envC env))
    end 
  in 
    match cnt with 
    | Cnt (Cnt0 c b) envV envC => 
        Nat.max (S c) (Nat.max (next_free b) 
          (Nat.max (next_free_envV envV) (next_free_cnt_envC envC)))
    | Cnt (Cnt1 c a b) envV envC => 
        Nat.max (S c) (Nat.max (S a) (Nat.max (next_free b) 
          (Nat.max (next_free_envV envV) (next_free_cnt_envC envC))))
    end.

Fixpoint next_free_envC env :=
  match env with
  | nil => 0 
  | (n, c) :: env => 
      Nat.max (S n) (Nat.max (next_free_cnt c) (next_free_envC env))
  end. *)

(* Definition is_int_val v := 
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

Definition is_either_val v := 
  match v with 
  | Left _ => True 
  | Right _ => True 
  | _ => False 
  end. *)

Inductive result :=
| Rhalt (v: value) (* End of program *)
| Rerr (* Type error *)
| Reoi (* End of Input *)
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
  | Var n => env ? n
  | Tree.Lit l => Some (Lit l)
  end.

(* Lemma get_val_env_com : forall a env env' n1 v1 n2 v2, n1 <> n2 -> 
  get_value_atom (env + (n1, v1) + (n2, v2) <++> env') a = get_value_atom (env + (n2, v2) + (n1, v1) <++> env') a.
Proof.
  repeat reduce || env.
Qed.

Lemma get_val_env_dup : forall a env env' n v v',
  get_value_atom ((env + (n, v') + (n, v)) <++> env') a = get_value_atom ((env + (n, v)) <++> env') a.
Proof.
  repeat reduce || env.
Qed.

Ltac rewrite_get_val := 
  match goal with
  | [ |- context[get_value_atom ((_ + (?n, _) + (?n, _)) <++> _) _]] => 
        rewrite get_val_env_dup
  | [H: ?n1 <> ?n2 |- context[get_value_atom (_ + (?n1, _) + (?n2, _) <++> _) ?a]] => 
        poseNew (Mark (n1, n2, a) "rewriting get_value_atom");
        rewrite (get_val_env_com a _ _ _ _ _ _ H)
  | [H: ?n1 = ?n2 -> False |- context[get_value_atom (_ + (?n1, _) + (?n2, _) <++> _) ?a]] => 
        poseNew (Mark (n1, n2, a) "rewriting get_value_atom");
        rewrite (get_val_env_com a _ _ _ _ _ _ H)
  end. *)

Definition binary_op_atom env op a1 a2 := 
  let v1 := get_value_atom env a1 in
  let v2 := get_value_atom env a2 in 
    match v1, v2 with 
    | Some v1, Some v2 => compute_binary_op op v1 v2 
    | _, _ => None 
    end.

(* Lemma binary_env_com : forall a1 a2 op env env' n1 v1 n2 v2, n1 <> n2 ->
  binary_op_atom (env + (n1, v1) + (n2, v2) <++> env') op a1 a2 = binary_op_atom (env + (n2, v2) + (n1, v1) <++> env') op a1 a2.
Proof.
  unfold binary_op_atom.
  intros.
  repeat rewrite_get_val; auto.
Qed.

Lemma binary_env_dup : forall a1 a2 op env env' n v v',
  binary_op_atom ((env + (n, v') + (n, v)) <++> env') op a1 a2 = binary_op_atom ((env + (n, v)) <++> env') op a1 a2.
Proof.
  intros.
  unfold binary_op_atom.
  repeat rewrite_get_val; auto.
Qed.

Ltac rewrite_binary_op := 
  match goal with
  | [ |- context[binary_op_atom ((_ + (?n, _) + (?n, _)) <++> _) _ _ _]] => 
        rewrite binary_env_dup
  | [H: ?n1 <> ?n2 |- context[binary_op_atom (_ + (?n1, _) + (?n2, _) <++> _) _ ?a1 ?a2]] => 
        poseNew (Mark (n1, n2, a1, a2) "rewriting binary_op_atom");
        rewrite (binary_env_com a1 a2 _ _ _ _ _ _ _ H)
  | [H: ?n1 = ?n2 -> False |- context[binary_op_atom (_ + (?n1, _) + (?n2, _) <++> _) _ ?a1 ?a2]] => 
        poseNew (Mark (n1, n2, a1, a2) "rewriting binary_op_atom");
        rewrite (binary_env_com a1 a2 _ _ _ _ _ _ _ H)
  end. *)

Definition unary_op_atom env op a := 
  let v := get_value_atom env a in 
    match v with 
    | Some v => compute_unary_op op v
    | _ => None 
    end.

(* Lemma unary_env_com : forall a op env env' n1 v1 n2 v2, n1 <> n2 ->
  unary_op_atom (env + (n1, v1) + (n2, v2) <++> env') op a = unary_op_atom (env + (n2, v2) + (n1, v1) <++> env') op a.
Proof.
  intros.
  unfold unary_op_atom.
  rewrite_get_val; auto.
Qed.

Lemma unary_env_dup : forall a op env env' n v v',
  unary_op_atom ((env + (n, v') + (n, v)) <++> env') op a = unary_op_atom ((env + (n, v)) <++> env') op a.
Proof.
  intros.
  unfold unary_op_atom.
  rewrite_get_val; auto.
Qed.

Ltac rewrite_unary_op := 
  match goal with
  | [ |- context[unary_op_atom ((_ + (?n, _) + (?n, _)) <++> _) _ _]] => 
        rewrite unary_env_dup
  | [H: ?n1 <> ?n2 |- context[unary_op_atom (_ + (?n1, _) + (?n2, _) <++> _) _ ?a]] => 
        poseNew (Mark (n1, n2, a) "rewriting unary_op_atom");
        rewrite (unary_env_com a _ _ _ _ _ _ _ H)
  | [H: ?n1 = ?n2 -> False |- context[unary_op_atom (_ + (?n1, _) + (?n2, _) <++> _) _ ?a]] => 
        poseNew (Mark (n1, n2, a) "rewriting unary_op_atom");
        rewrite (unary_env_com a _ _ _ _ _ _ _ H)
  end.

Ltac rewrite_op := 
  rewrite_get_val || rewrite_unary_op || rewrite_binary_op. *)

Function evalₜ (fuel : nat) (envV : env value) (envC : env cntV) (t : term) (io : IO) : result * IO := 
  match fuel with
  | 0 => (Rtimeout, io)
  | S fuel => 
      match t with
      | LetB n op a1 a2 r => 
          match binary_op_atom envV op a1 a2 with 
          | Some v => evalₜ fuel (envV + (n, v)) envC r io 
          | _ => (Rerr, io)
          end 
      | LetU n op a r => 
          match unary_op_atom envV op a with 
          | Some v => evalₜ fuel (envV + (n, v)) envC r io
          | _ => (Rerr, io)
          end 
      | LetC (Cnt0 n b) r => 
          let c := Cnt0 n b in 
          evalₜ fuel envV (envC + (n, Cnt c envV envC)) r io 
      | LetC (Cnt1 n a b) r => 
          let c := Cnt1 n a b in 
          evalₜ fuel envV (envC + (n, Cnt c envV envC)) r io
      | LetF (Fnt fname retC farg fbody) r => 
          let f := Fnt fname retC farg fbody in 
          evalₜ fuel (envV + (fname, Fun f envV)) envC r io 
      | LetIn n r => 
          match get_input io with
          | Some (i, io) => evalₜ fuel (envV + (n, Lit (IntLit i))) envC r io
          | _ => (Reoi, io)
          end 
      | LetOut n a r => 
          match get_value_atom envV a with 
          | Some (Lit (IntLit o)) => evalₜ fuel (envV + (n, Lit UnitLit)) envC r (outputs io o)
          | _ => (Rerr, io)
          end
      | AppC0 n => 
          match envC ? n with 
          | Some (Cnt (Cnt0 _ b) envV envC) => 
              let cnt := Cnt (Cnt0 n b) envV envC in 
              evalₜ fuel envV (envC + (n, cnt)) b io 
          | _ => (Rerr, io)
          end 
      | AppC1 n a => 
          match envC ? n with 
          | Some (Cnt (Cnt1 _ carg b) cenv cenvC) => 
              let cnt := Cnt (Cnt1 n carg b) cenv cenvC in
              match get_value_atom envV a with 
              | Some v => evalₜ fuel (cenv + (carg, v)) (cenvC + (n, cnt)) b io 
              | _ => (Rerr, io)
              end
          | _ => (Rerr, io)
          end
      | AppF f c a => 
          match get_value_atom envV a with
          | Some (Fun (Fnt fname retC farg fbody) fenv) => 
              let f := Fnt fname retC farg fbody in
              match envC ? c with
              | Some (Cnt (Cnt1 _ carg cbody) cenv cenvC) => 
                  let cnt := Cnt (Cnt1 c carg cbody) cenv cenvC in 
                  match get_value_atom envV a with
                  | Some v => 
                      evalₜ fuel (fenv + (fname, Fun f fenv) + (farg, v)) (empty + (c, cnt)) fbody io
                  | _ => (Rerr, io)
                  end 
              | _ => (Rerr, io)
              end 
          | _ => (Rerr, io)
          end
      | Ite c t e => 
          match get_value_atom envV c with
          | Some (Lit (BoolLit true)) => 
              evalₜ fuel envV envC (AppC0 t) io 
          | Some (Lit (BoolLit false)) => 
              evalₜ fuel envV envC (AppC0 e) io 
          | _ => (Rerr, io)
          end 
      | Match s lc rc => 
          match get_value_atom envV s with 
          | Some (Left v) => 
              match envC ? lc with 
              | Some (Cnt (Cnt1 _ carg b) envV envC) => 
                  let cnt := Cnt (Cnt1 lc carg b) envV envC in 
                  evalₜ fuel (envV + (carg, v)) (envC + (lc, cnt)) b io 
              | _ => (Rerr, io)
              end
          | Some (Right v) => 
              match envC ? rc with 
              | Some (Cnt (Cnt1 _ carg b) envV envC) => 
                  let cnt := Cnt (Cnt1 rc carg b) envV envC in 
                  evalₜ fuel (envV + (carg, v)) (envC + (rc, cnt)) b io 
              | _ => (Rerr, io)
              end 
          | _ => (Rerr, io)
          end 
      | Halt a => 
          match get_value_atom envV a with 
          | Some v => (Rhalt v, io)
          | _ => (Rerr, io)
          end
      end
  end.

(* Ltac eval_env_intanciate_IH IH :=
  match goal with
  | [|- context[evalₜ _ _ _ ?t _]] => 
      let Hdup := fresh "Hdup" in
      let Hcom := fresh "Hcom" in
      let Hcnt0dup := fresh "Hcnt0dup" in
      let Hcnt0com := fresh "Hcnt0com" in
      let Hcnt1dup := fresh "Hcnt1dup" in
      let Hcnt1com := fresh "Hcnt1com" in
      pose proof (IH t) as [Hdup [Hcom [Hcnt0dup [Hcnt0com [Hcnt1dup Hcnt1com]]]]];
      clear IH
  end.

Lemma eval_env : forall f t,
  (forall envV envV' envC io n v' v, 
    evalₜ f (envV + (n, v') + (n, v) <++> envV') envC t io = evalₜ f (envV + (n, v) <++> envV') envC t io 
  ) /\ (forall envV envV' envC io n1 n2 v1 v2, n1 <> n2 ->
    evalₜ f (envV + (n1, v1) + (n2, v2) <++> envV') envC t io = evalₜ f (envV + (n2, v2) + (n1, v1) <++> envV') envC t io
  ) /\ (forall envV envC envC' io nc bc envVc envVc' envCc n v v',
    evalₜ f envV (envC + (nc, Cnt (Cnt0 nc bc) (envVc + (n, v') + (n, v) <++> envVc') envCc) <++> envC') t io
    = evalₜ f envV (envC + (nc, Cnt (Cnt0 nc bc) (envVc + (n, v) <++> envVc') envCc) <++> envC') t io
  ) /\ (forall envV envC envC' io nc bc envVc envVc' envCc n1 n2 v1 v2, n1 <> n2 ->
    evalₜ f envV (envC + (nc, Cnt (Cnt0 nc bc) (envVc + (n1, v1) + (n2, v2) <++> envVc') envCc) <++> envC') t io
    = evalₜ f envV (envC + (nc, Cnt (Cnt0 nc bc) (envVc + (n2, v2) + (n1, v1) <++> envVc') envCc) <++> envC') t io
  ) /\ (forall envV envC envC' io nc ac bc envVc envVc' envCc n v v',
    evalₜ f envV (envC + (nc, Cnt (Cnt1 nc ac bc) (envVc + (n, v') + (n, v) <++> envVc') envCc) <++> envC') t io
    = evalₜ f envV (envC + (nc, Cnt (Cnt1 nc ac bc) (envVc + (n, v) <++> envVc') envCc) <++> envC') t io
  ) /\ (forall envV envC envC' io nc ac bc envVc envVc' envCc n1 n2 v1 v2, n1 <> n2 ->
    evalₜ f envV (envC + (nc, Cnt (Cnt1 nc ac bc) (envVc + (n1, v1) + (n2, v2) <++> envVc') envCc) <++> envC') t io
    = evalₜ f envV (envC + (nc, Cnt (Cnt1 nc ac bc) (envVc + (n2, v2) + (n1, v1) <++> envVc') envCc) <++> envC') t io
  ).
Proof.
  induction f, t; try solve [
    repeat reduce || rewrite_op || env || destruct_match || eval_env_intanciate_IH IHf
  ]; simpl.
  all: try eval_env_intanciate_IH IHf.
  - repeat reduce || rewrite_op || destruct_match || env.
    * pose proof (Hcnt0dup (envV + (n, v') + (n, v) <++> envV') envC { } io 
        name body envV envV' envC n v v'
      ).
      repeat env; rewrite_any; auto.
    * pose proof (Hcnt1dup (envV + (n, v') + (n, v) <++> envV') envC { } io 
        name arg body envV envV' envC n v v'
      ).
      repeat env; rewrite_any; auto.
    * pose proof (Hcnt0com (envV + (n1, v1) + (n2, v2) <++> envV') envC { } io 
        name body envV envV' envC n1 n2 v1 v2 H
      ).
      repeat env; rewrite_any; auto.
    * pose proof (Hcnt1com (envV + (n1, v1) + (n2, v2) <++> envV') envC { } io 
        name arg body envV envV' envC n1 n2 v1 v2 H
      ).
      repeat env; rewrite_any; auto.
    * rewrite Hcnt0dup.
      
      
      destruct (Nat.eq_dec name nc). 
      pose proof 
        (Hcnt0dup envV 
          (envC + (nc, Cnt (Cnt0 nc bc) (envVc + (n, v') + (n, v) <++> envVc') envCc))
          io name body
        ).
  - rewrite binary_env_com; auto.
    repeat reduce || destruct_match.
    rewrite 2 add_update.
    pose proof (IHf t) as [? ?]; auto.
  - rewrite unary_env_dup.
    repeat destruct_match || reduce.
    rewrite 2 add_update.
    pose proof (IHf t) as [? ?]; auto.
  - rewrite unary_env_com; auto.
    repeat destruct_match || reduce.
    rewrite 2 add_update.
    pose proof (IHf t) as [? ?]; auto.
  -
     admit.
  - admit.
  - admit.
  - admit.
  - repeat reduce || destruct_match.
    rewrite 2 add_update.
    pose proof (IHf t) as [? ?]; auto.
  - repeat reduce || destruct_match.
    rewrite 2 add_update.
    pose proof (IHf t) as [? ?]; auto.
  - rewrite get_val_env_dup.
    repeat reduce || destruct_match.
    rewrite 2 add_update.
    pose proof (IHf t) as [? ?]; auto.
  - rewrite get_val_env_com; auto.
    repeat reduce || destruct_match.
    rewrite 2 add_update.
    pose proof (IHf t) as [? ?]; auto.
  - rewrite get_val_env_dup.
    repeat reduce || destruct_match.
  - rewrite get_val_env_com;
    repeat reduce || destruct_match.
  - rewrite get_val_env_dup.
    repeat reduce || destruct_match.
  - rewrite get_val_env_com;
    repeat reduce || destruct_match.
  - rewrite get_val_env_dup.
    repeat reduce || destruct_match.
    * pose proof (IHf (AppC0 thenC)) as [? ?]; auto.
    * pose proof (IHf (AppC0 elseC)) as [? ?]; auto.
  - rewrite get_val_env_com;
    repeat reduce || destruct_match.
    * pose proof (IHf (AppC0 thenC)) as [? ?]; auto.
    * pose proof (IHf (AppC0 elseC)) as [? ?]; auto.
  - rewrite get_val_env_dup.
    repeat reduce || destruct_match.
  - rewrite get_val_env_com;
    repeat reduce || destruct_match.
  - rewrite get_val_env_dup.
    repeat reduce || destruct_match.
  - rewrite get_val_env_com;
    repeat reduce || destruct_match.
Qed. *)

(* Lemma eval_env_dup : forall f t envV envC io n v' v, 
  evalₜ f (envV + (n, v') + (n, v)) envC t io = evalₜ f (envV + (n, v)) envC t io.
Proof.
  induction f, t; repeat reduce.
  - rewrite binary_env_dup.
    repeat destruct_match || reduce.

     rewrite IHf. 

Lemma eval_env_com : forall f t envV envC io n1 n2 v1 v2, n1 <> n2 ->
  evalₜ f (envV + (n1, v1) + (n2, v2)) envC t io = evalₜ f (envV + (n2, v2) + (n1, v1)) envC t io.
Proof.
  induction f, t; repeat reduce.
  - rewrite binary_env_com; auto.
    repeat reduce || destruct_match.
    destruct (Nat.eq_dec name n1), (Nat.eq_dec name n2).
    *  *)
          
(* Reserved Notation "'{' io1 '|' '(' Γᵥ ',' Γᵨ ')' '}' t '~>(' f ')' '{' r ',' io2 '}'" (at level 70, no associativity).
Inductive eval : env value -> env (cnt * (env value)) -> term -> IO -> nat -> result -> IO -> Prop :=
| eval_letB : forall envV envC n op a1 a2 rest io f v r io',
    binary_op_atom envV op a1 a2 = Some v ->
    { io | (envV + (n, v), envC) } rest ~>(f) { r, io' } ->
      { io | (envV, envC) } LetB n op a1 a2 rest ~>(f + 1) { r, io' }
| eval_letB_err : forall envV envC n op a1 a2 rest io,
    binary_op_atom envV op a1 a2 = None ->
      { io | (envV, envC) } LetB n op a1 a2 rest ~>(1) { Rerr, io }
| eval_letU : forall envV envC n op a rest io f v r io',
    unary_op_atom envV op a = Some v ->
    { io | (envV + (n, v), envC) } rest ~>(f) { r, io' } ->
      { io | (envV, envC) } LetU n op a rest ~>(f + 1) { r, io' }
| eval_letU_err : forall envV envC n op a rest io,
    unary_op_atom envV op a = None ->
      { io | (envV, envC) } LetU n op a rest ~>(1) { Rerr, io }
| eval_letC0 : forall envV envC cname cbody rest io f r io',
    let cnt := Cnt0 cname cbody in 
    { io | (envV, envC + (cname, (cnt, envV))) } rest ~>(f) { r, io' } ->
      { io | (envV, envC) } LetC cnt rest ~>(f + 1) { r, io' }
| eval_letC1 : forall envV envC cname carg cbody rest io f r io',
    let cnt := Cnt1 cname carg cbody in 
    { io | (envV, envC + (cname, (cnt, envV))) } rest ~>(f) { r, io' } ->
      { io | (envV, envC)} LetC cnt rest ~>(f + 1) { r, io' }
| eval_letF : forall envV envC fname fretC farg fbody rest io f r io',
    let fnt := Fnt fname fretC farg fbody in
    { io | (envV + (fname, Fun fnt envV), envC) } rest ~>(f) { r, io' } ->
      { io | (envV, envC) } LetF fnt rest ~>(f + 1) { r, io' }
| eval_letIn : forall envV envC n rest i is os f r io',
    { {|input:=is;output:=os|} | (envV + (n, Lit (IntLit i)), envC) } rest ~>(f) { r, io' } ->
      { {|input:=i::is;output:=os|} | (envV, envC) } LetIn n rest ~>(f + 1) { r, io' }
| eval_letIn_err : forall envV envC n rest os,
    let io := {|input:=nil;output:=os|} in
      { io | (envV, envC) } LetIn n rest ~>(1) { Reoi, io }
| eval_letOut : forall envV envC n a rest is os f r io' o,
    get_value_atom envV a = Some (Lit (IntLit o)) -> 
    { {|input:=is;output:=o::os|} | (envV + (n, Lit UnitLit), envC) } rest ~>(f) { r, io' } ->
      {  {|input:=is;output:=os|} | (envV, envC) } LetOut n a rest ~>(f + 1) { r, io' }
| eval_letOut_err : forall envV envC n a rest io,
    get_value_atom envV a = None ->
      { io | (envV, envC) } LetOut n a rest ~>(1) { Rerr, io }
| eval_letOut_err' : forall envV envC n a rest io v,
    ~ (is_int_val v) ->
    get_value_atom envV a = Some v ->
      { io | (envV, envC) } LetOut n a rest ~>(1) { Rerr, io }
| eval_AppC0 : forall envV envC c cbody envV' io f r io',
    get_cnt0 envC c = Some (Cnt0 c cbody, envV') ->
    { io | (envV', empty) } cbody ~>(f) { r, io' } ->
      { io | (envV, envC) } AppC0 c ~>(f + 1) { r, io' }
| eval_AppC0_err : forall envV envC c io,
    get_cnt0 envC c = None ->
      { io | (envV, envC) } AppC0 c ~>(1) { Rerr, io }
| eval_AppC1 : forall envV envC c a v cbody carg envV' io f r io',
    get_cnt1 envC c = Some (Cnt1 c carg cbody, envV') ->
    get_value_atom envV a = Some v ->
    { io | (envV' + (carg, v), empty) } cbody ~>(f) { r, io' } ->
      { io | (envV, envC) } AppC1 c a ~>(f + 1) { r, io' }
| eval_AppC1_err : forall envV envC c a io,
    get_cnt1 envC c = None ->
      { io | (envV, envC) } AppC1 c a ~>(1) { Rerr, io }
| eval_AppC1_err' : forall envV envC c a cbody carg envV' io,
    get_cnt1 envC c = Some (Cnt1 c carg cbody, envV') ->
    get_value_atom envV a = None ->
      { io | (envV, envC) } AppC1 c a ~>(1) { Rerr, io }
| eval_AppF : forall envV envC af fname fretC farg fbody fenv c carg cbody cenv a v io f r io',
    let fnt := Fnt fname fretC farg fbody in
    let cnt := Cnt1 c carg cbody in
    get_value_atom envV af = Some (Fun fnt fenv) ->
    get_value_atom envV a = Some v ->
    get_cnt1 envC c = Some (cnt, cenv) ->
    { io | (fenv + (fname, Fun fnt fenv) + (farg, v), empty + (fretC, (cnt, cenv))) } fbody ~>(f) { r, io' } ->
      { io | (envV, envC) } AppF af c a ~>(f + 1) { r, io' }
| eval_AppF_err : forall envV envC af c a io,
    get_value_atom envV af = None ->
      { io | (envV, envC) } AppF af c a ~>(1) { Rerr, io }
| eval_AppF_err' : forall envV envC af c a io v,
    ~ (is_fun_val v) -> 
    get_value_atom envV af = Some v ->
      { io | (envV, envC) } AppF af c a ~>(1) { Rerr, io }
| eval_AppF_err'' : forall envV envC af c a io fname fretC farg fbody fenv,
    let fnt := Fnt fname fretC farg fbody in
    get_value_atom envV af = Some (Fun fnt fenv) ->
    get_value_atom envV a = None ->
      { io | (envV, envC) } AppF af c a ~>(1) { Rerr, io }
| eval_AppF_err''' : forall envV envC af c a io fname fretC farg fbody fenv v,
    let fnt := Fnt fname fretC farg fbody in
    get_value_atom envV af = Some (Fun fnt fenv) ->
    get_value_atom envV a = Some v ->
    get_cnt1 envC c = None ->
      { io | (envV, envC) } AppF af c a ~>(1) { Rerr, io }
| eval_Ite_true : forall envV envC c thenC elseC cbody cenv io f r io',
    let cnt := Cnt0 thenC cbody in 
    get_value_atom envV c = Some (Lit (BoolLit true)) ->
    get_cnt0 envC thenC = Some (cnt, cenv) ->
    { io | (cenv, empty) } cbody ~>(f) { r, io' } ->
      { io | (envV, envC) } Ite c thenC elseC ~>(f + 1) { r, io' }
| eval_Ite_true_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = Some (Lit (BoolLit true)) ->
    get_cnt0 envC thenC = None ->
      { io | (envV, envC) } Ite c thenC elseC ~>(1) { Rerr, io }
| eval_Ite_false : forall envV envC c thenC elseC cbody cenv io f r io',
    let cnt := Cnt0 elseC cbody in 
    get_value_atom envV c = Some (Lit (BoolLit false)) ->
    get_cnt0 envC elseC = Some (cnt, cenv) ->
    { io | (cenv, empty) } cbody ~>(f) { r, io' } ->
      { io | (envV, envC) } Ite c thenC elseC ~>(f + 1) { r, io' }
| eval_Ite_false_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = Some (Lit (BoolLit false)) ->
    get_cnt0 envC elseC = None ->
      { io | (envV, envC) } Ite c thenC elseC ~>(1) { Rerr, io }
| eval_Ite_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = None ->
      { io | (envV, envC) } Ite c thenC elseC ~>(1) { Rerr, io }
| eval_Ite_err' : forall envV envC c thenC elseC io v,
    ~ (is_bool_val v) ->
    get_value_atom envV c = Some v ->
      { io | (envV, envC) } Ite c thenC elseC ~>(1) { Rerr, io }
| eval_match_left : forall envV envC scrut lc larg lbody lenv rc v io f r io',
    let lcnt := Cnt1 lc larg lbody in
    get_value_atom envV scrut = Some (Left v) ->
    get_cnt1 envC lc = Some (lcnt, lenv) ->
    { io | (lenv + (larg, v), empty) } lbody ~>(f) { r, io' } ->
      { io | (envV, envC) } Match scrut lc rc ~>(f + 1) { r, io' }
| eval_match_right : forall envV envC scrut lc rc rarg rbody renv v io f r io',
    let rcnt := Cnt1 rc rarg rbody in
    get_value_atom envV scrut = Some (Right v) ->
    get_cnt1 envC rc = Some (rcnt, renv) ->
    { io | (renv + (rarg, v), empty) } rbody ~>(f) { r, io' } ->
      { io | (envV, envC) } Match scrut lc rc ~>(f + 1) { r, io' }
| eval_match_err : forall envV envC scrut lc rc io,
    get_value_atom envV scrut = None ->
      { io | (envV, envC) } Match scrut lc rc ~>(1) { Rerr, io }
| eval_match_err' : forall envV envC scrut lc rc v io,
    ~ (is_either_val v) ->
    get_value_atom envV scrut = Some v ->
      { io | (envV, envC) } Match scrut lc rc ~>(1) { Rerr, io }
| eval_match_left_err : forall envV envC scrut lc rc v io,
    get_value_atom envV scrut = Some (Left v) ->
    get_cnt1 envC lc = None ->
      { io | (envV, envC) } Match scrut lc rc ~>(1) { Rerr, io }
| eval_match_right_err : forall envV envC scrut lc rc v io,
    get_value_atom envV scrut = Some (Right v) ->
    get_cnt1 envC rc = None ->
      { io | (envV, envC) } Match scrut lc rc ~>(1) { Rerr, io }
| eval_halt : forall envV envC a v io,
    get_value_atom envV a = Some v ->
      { io | (envV, envC) } Halt a ~>(1) { Rhalt v, io }
| eval_halt_err : forall envV envC a io,
    get_value_atom envV a = None ->
      { io | (envV, envC) } Halt a ~>(1) { Rerr, io }
| eval_timeout : forall envV envC t io,
      { io | (envV, envC) } t ~>(0) { Rtimeout, io }
| eval_extra_fuel : forall envV envC t io f r io',
    r <> Rtimeout ->
    { io | (envV, envC) } t ~>(f) { r, io' } ->
      { io | (envV, envC) } t ~>(f + 1) { r, io' }
where "'{' io1 '|' '(' Γᵥ ',' Γᵨ ')' '}' t '~>(' f ')' '{' r ',' io2 '}'" := (eval Γᵥ Γᵨ t io1 f r io2) : cps_scope.

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
  { io | (envV, envC) } t ~>(f') { r, io' }.
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
  - (* Match *)
    destruct (get_value_atom envV scrut) eqn:V; try total_ind_solve_error_case.
    destruct v;
    try solve [
      exists Rerr, io;
      apply (eval_min_fuel' 1); eauto with eval lia; [
      intro; discriminate H |
      eapply eval_match_err'; eauto;
      unfold is_either_val; auto]
    ].
    + (* Left *)
      destruct (get_cnt1 envC lc) eqn:C; try total_ind_solve_error_case.
      destruct p. destruct c; try solve [
      unfold get_cnt1 in C; repeat destruct_match; invert C]. 
      assert (lc = name). {
        unfold get_cnt1 in C.
        repeat destruct_match; invert C.
        apply Nat.eqb_eq; auto.
      }
      subst.
      specialize (IHf _ body (Env.add e arg v) empty io A) as [r [io' ?]].
      eauto with eval.
    + (* Right *)
      destruct (get_cnt1 envC rc) eqn:C; try total_ind_solve_error_case.
      destruct p. destruct c; try solve [
      unfold get_cnt1 in C; repeat destruct_match; invert C]. 
      assert (rc = name). {
        unfold get_cnt1 in C.
        repeat destruct_match; invert C.
        apply Nat.eqb_eq; auto.
      }
      subst.
      specialize (IHf _ body (Env.add e arg v) empty io A) as [r [io' ?]].
      eauto with eval.
  - (* Halt *) 
    destruct (get_value_atom envV a) eqn:V; try total_ind_solve_error_case.
    exists (Rhalt v), io.
    eapply (eval_min_fuel' 1); eauto with eval lia.
    intro H; discriminate H.
Qed.

Theorem eval_total : forall f t envV envC io, exists r io',
  { io | (envV, envC) } t ~>(f) { r, io' }.
Proof.
  eauto using eval_total_ind.
Qed.

Lemma eval_eoi: forall io envV envC t f io' r, r = Reoi ->
  { io | (envV, envC) } t ~>(f) { r, io' } ->
    input io' = nil.
Proof.
  induction 2; auto; discriminate H.
Qed. *)
