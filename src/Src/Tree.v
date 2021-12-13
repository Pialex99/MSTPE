From Common Require Export Literal Primitive.

(* Inductive type : Set := 
| Int | Bool | Unit 
| Tuple (tpe1 tpe2: type) 
| Fnt (args: list type) (rettpe: type)
| Sum (ltpe rtpe : type). *)

(* Record arg : Set := {name: nat;tpe: type}. *)

Inductive term : Set := 
| Var (n: nat)
| Const (l: literal)
| Let (x: nat) (t rest : term)
(* | Let (x: arg) (t rest : term) *)
(* | LetRec (funs: list fnt) (rest : term) *)
| LetRec (f: fnt) (rest : term)
| App (f t : term)
| In
| Out (t: term)
(* | Halt (t: term) *)
| Ite (cond thent elset: term)
| BinaryOp (op: binary_primitives) (t1 t2: term)
| UnaryOp (op: unary_primitives) (t: term)
| Match (scrut: term) (lcase: nat * term) (rcase: nat * term) 
(* | NewRef (tpe: type) (t: term)
| UpdateRef (ref t: term)
| ReadRef (ref: term) *)
with 
  fnt : Set := Fnt (fname: nat) (arg: nat) (body: term).
  (* fnt : Set := Fnt (fname: nat) (args: list arg) (rettpe: type) (body: term). *)

Fixpoint next_freeₜ (t : term) : nat := 
  match t with 
  | Var n => S n 
  | Const _ => 0
  | Let x t r => max (next_freeₜ t) (max (next_freeₜ r) (S x))
  | LetRec (Fnt n a b) r => 
      max (S n) (max (S a) (max (next_freeₜ b) (next_freeₜ r)))
  | App f t => max (next_freeₜ f) (next_freeₜ t)
  | In => 0 
  | Out t => next_freeₜ t
  | Ite c t e => max (next_freeₜ c) (max (next_freeₜ t) (next_freeₜ e))
  | BinaryOp _ t1 t2 => max (next_freeₜ t1) (next_freeₜ t2)
  | UnaryOp _ t => next_freeₜ t 
  | Match s (ln, lt) (rn, rt) => 
      max (next_freeₜ s) (max (S ln) (max (next_freeₜ lt) (max (S rn) (next_freeₜ rt))))
  end.