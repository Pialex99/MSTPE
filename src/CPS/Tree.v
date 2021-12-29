From Common Require Export Literal Primitive.
From Utils Require Import Env Tactics.

Inductive atom := Var (n: nat) | Lit (lit: literal).

Inductive term :=
| LetB (name: nat) (op: binary_primitives) (a1 a2: atom) (rest: term) 
| LetU (name: nat) (op: unary_primitives) (a: atom) (rest: term) 
| LetC (cont: cnt) (rest: term)
| LetF (f: fnt) (rest: term) 
| LetIn (name: nat) (rest: term)
| LetOut (n:nat) (a: atom) (rest: term) (* We need n (which is always unit) because Out returns unit *)
| AppC0 (name: nat) 
| AppC1 (name: nat) (a: atom)
| AppF (f: atom) (retC: nat) (a: atom)
| Ite (c: atom) (thenC elseC: nat)
| Match (scrut: atom) (lc rc: nat)
| Halt (a: atom)
with 
  cnt := Cnt0 (name: nat) (body: term) | Cnt1 (name arg: nat) (body: term)
with 
  fnt := Fnt (name retC arg: nat) (body: term).

Definition nf_atom a := 
  match a with
  | Var n => S n 
  | Lit _ => 0 
  end.

Fixpoint next_free t := 
  match t with  
  | LetB n _ a1 a2 r => 
      Nat.max (S n) (Nat.max (nf_atom a1) (Nat.max (nf_atom a2) (next_free r)))
  | LetU n _ a r => 
      Nat.max (S n) (Nat.max (nf_atom a) (next_free r))
  | LetC (Cnt0 n b) r => 
      Nat.max (S n) (Nat.max (next_free b) (next_free b))
  | LetC (Cnt1 n a b) r => 
      Nat.max (S n) (Nat.max (S a) (Nat.max (next_free b) (next_free r)))
  | LetF (Fnt n c a b) r => 
      Nat.max (S n) (Nat.max (S c) (Nat.max (S a) (Nat.max (next_free b) (next_free r))))
  | LetIn n r => 
      Nat.max (S n) (next_free r)
  | LetOut n a r => 
      Nat.max (S n) (Nat.max (nf_atom a) (next_free r))
  | AppC0 n => S n 
  | AppC1 n a => Nat.max (S n) (nf_atom a)
  | AppF f c a => Nat.max (nf_atom f) (Nat.max (S c) (nf_atom a))
  | Ite c t e => Nat.max (nf_atom c) (Nat.max (S t) (S e))
  | Match s lc rc => Nat.max (nf_atom s) (Nat.max (S lc) (S rc))
  | Halt a => nf_atom a 
  end.

Fixpoint size t :=
  match t with
  | LetB _ _ _ _ r => 1 + size r 
  | LetU _ _ _ r => 1 + size r 
  | LetC (Cnt0 _ b) r => 1 + size b + size r 
  | LetC (Cnt1 _ _ b) r => 1 + size b + size r
  | LetF (Fnt _ _ _ b) r => 1 + size b + size r
  | LetIn _ r => 1 + size r
  | LetOut _ _ r => 1 + size r
  | AppC0 _ => 1 
  | AppC1 _ _ => 1
  | AppF _ _ _ => 1 
  | Ite _ _ _ => 1
  | Match _ _ _ => 1
  | Halt _ => 1
  end.

Lemma size_t_gt_1 : forall t, 0 < size t.
Proof.
  induction t; reduce; destruct_match; lia.
Qed.

Section Renameₜ.
  Variable e : env nat.

  Definition get_or_id (n : nat) := 
    match e ? n with 
    | Some n => n
    | None => n
    end.

  Definition renameₐ (a : atom) := 
    match a with 
    | Var n => Var (get_or_id n)
    | Lit _ => a
    end.

  Fixpoint renameₜ (t : term) := 
    match t with 
    | LetB n op a1 a2 r => 
        let n := get_or_id n in
        let a1 := renameₐ a1 in 
        let a2 := renameₐ a2 in 
        let r := renameₜ r in
          LetB n op a1 a2 r
    | LetU n op a r =>
        let n := get_or_id n in
        let a := renameₐ a in
        let r := renameₜ r in
          LetU n op a r
    | LetC (Cnt0 n b) r => 
        let n := get_or_id n in
        let b := renameₜ b in
        let r := renameₜ r in
          LetC (Cnt0 n b) r
    | LetC (Cnt1 n a b) r =>
        let n := get_or_id n in
        let a := get_or_id a in
        let b := renameₜ b in
        let r := renameₜ r in
          LetC (Cnt1 n a b) r
    | LetF (Fnt n c a b) r => 
        let n := get_or_id n in
        let c := get_or_id c in
        let a := get_or_id a in
        let b := renameₜ b in
        let r := renameₜ r in
          LetF (Fnt n c a b) r 
    | LetIn n r =>
        let n := get_or_id n in
        let r := renameₜ r in
          LetIn n r
    | LetOut n a r =>
        let n := get_or_id n in
        let a := renameₐ a in
        let r := renameₜ r in
          LetOut n a r
    | AppC0 n =>
        let n := get_or_id n in
          AppC0 n 
    | AppC1 n a =>
        let n := get_or_id n in
        let a := renameₐ a in
          AppC1 n a
    | AppF f c a =>
        let f := renameₐ f in
        let c := get_or_id c in
        let a := renameₐ a in
          AppF f c a 
    | Ite c t e =>
        let c := renameₐ c in
        let t := get_or_id t in
        let e := get_or_id e in
          Ite c t e
    | Match s lc rc =>
        let s := renameₐ s in
        let lc := get_or_id lc in
        let rc := get_or_id rc in
          Match s lc rc
    | Halt a =>
        let a := renameₐ a in
          Halt a
    end.
End Renameₜ.

Lemma get_or_id_empty : forall n, 
  get_or_id { } n = n.
Proof. reduce. Qed.

Lemma rename_a_empty : forall a,
  renameₐ { } a = a.
Proof.
  destruct a; reduce.
Qed.

Lemma rename_t_empty_ind : forall n t, size t < n ->
  renameₜ { } t = t.
Proof.
  induction n, t; repeat reduce || destruct_match || simpl_lia.
  all: repeat rewrite get_or_id_empty || rewrite rename_a_empty; reduce.
  all: repeat rewrite IHn; auto with lia.
Qed.

Lemma rename_t_empty : forall t, 
  renameₜ { } t = t.
Proof.
  eauto using rename_t_empty_ind.
Qed.