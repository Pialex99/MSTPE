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
