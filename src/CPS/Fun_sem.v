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
    lookup envC c = Some (Cnt0 c cbody, envV') ->
    eval envV' empty cbody io f r io' ->
      eval envV envC (AppC0 c) io (f + 1) r io'
| eval_AppC0_err : forall envV envC c io,
    lookup envC c = None ->
      eval envV envC (AppC0 c) io 1 Rerr io
| eval_AppC1 : forall envV envC c a v cbody carg envV' io f r io',
    lookup envC c = Some (Cnt1 c carg cbody, envV') ->
    get_value_atom envV a = Some v ->
    eval (Env.add envV' carg v) empty cbody io f r io' ->
      eval envV envC (AppC1 c a) io (f + 1) r io'
| eval_AppC1_err : forall envV envC c a io,
    lookup envC c = None ->
      eval envV envC (AppC1 c a) io 1 Rerr io
| eval_AppC1_err' : forall envV envC c a cbody carg envV' io,
    lookup envC c = Some (Cnt1 c carg cbody, envV') ->
    get_value_atom envV a = None ->
      eval envV envC (AppC1 c a) io 1 Rerr io
| eval_AppF : forall envV envC af fname fretC farg fbody fenv c carg cbody cenv a v io f r io',
    let fnt := Fnt fname fretC farg fbody in
    let cnt := Cnt1 c carg cbody in
    get_value_atom envV af = Some (Fun fnt fenv) ->
    get_value_atom envV a = Some v ->
    lookup envC c = Some (cnt, cenv) ->
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
    lookup envC c = None ->
      eval envV envC (AppF af c a) io 1 Rerr io
| eval_Ite_true : forall envV envC c thenC elseC cbody cenv io f r io',
    let cnt := Cnt0 thenC cbody in 
    get_value_atom envV c = Some (Lit (BoolLit true)) ->
    lookup envC thenC = Some (cnt, cenv) ->
    eval cenv empty cbody io f r io' ->
      eval envV envC (Ite c thenC elseC) io (f + 1) r io'
| eval_Ite_true_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = Some (Lit (BoolLit true)) ->
    lookup envC thenC = None ->
      eval envV envC (Ite c thenC elseC) io 1 Rerr io
| eval_Ite_flase : forall envV envC c thenC elseC cbody cenv io f r io',
    let cnt := Cnt0 thenC cbody in 
    get_value_atom envV c = Some (Lit (BoolLit false)) ->
    lookup envC elseC = Some (cnt, cenv) ->
    eval cenv empty cbody io f r io' ->
      eval envV envC (Ite c thenC elseC) io (f + 1) r io'
| eval_Ite_false_err : forall envV envC c thenC elseC io,
    get_value_atom envV c = Some (Lit (BoolLit false)) ->
    lookup envC elseC = None ->
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
      eval envV envC (Halt a) io 1 Rerr io.

