From Common Require Export Literal Primitive.

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
      max (S n) (max (nf_atom a1) (max (nf_atom a2) (next_free r)))
  | LetU n _ a r => 
      max (S n) (max (nf_atom a) (next_free r))
  | LetC (Cnt0 n b) r => 
      max (S n) (max (next_free b) (next_free b))
  | LetC (Cnt1 n a b) r => 
      max (S n) (max (S a) (max (next_free b) (next_free r)))
  | LetF (Fnt n c a b) r => 
      max (S n) (max (S c) (max (S a) (max (next_free b) (next_free r))))
  | LetIn n r => 
      max (S n) (next_free r)
  | LetOut n a r => 
      max (S n) (max (nf_atom a) (next_free r))
  | AppC0 n => S n 
  | AppC1 n a => max (S n) (nf_atom a)
  | AppF f c a => max (nf_atom f) (max (S c) (nf_atom a))
  | Ite c t e => max (nf_atom c) (max (S t) (S e))
  | Match s lc rc => max (nf_atom s) (max (S lc) (S rc))
  | Halt a => nf_atom a 
  end.