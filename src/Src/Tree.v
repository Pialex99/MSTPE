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

Fixpoint next_free (t : term) : nat := 
  match t with 
  | Var n => S n 
  | Const _ => 0
  | Let x t r => max (next_free t) (max (next_free r) (S x))
  | LetRec (Fnt n a b) r => 
      max (S n) (max (S a) (max (next_free b) (next_free r)))
  | App f t => max (next_free f) (next_free t)
  | In => 0 
  | Out t => next_free t
  | Ite c t e => max (next_free c) (max (next_free t) (next_free e))
  | BinaryOp _ t1 t2 => max (next_free t1) (next_free t2)
  | UnaryOp _ t => next_free t 
  | Match s (ln, lt) (rn, rt) => 
      max (next_free s) (max (S ln) (max (next_free lt) (max (S rn) (next_free rt))))
  end.

Fixpoint size t : nat := 
  match t with 
  | Var _ => 1 
  | Const _ => 1
  | Let _ t r => 1 + size t + size r 
  | LetRec (Fnt _ _ b) r => 1 + size b + size r
  | App f t => 1 + size f + size t 
  | In => 1 
  | Out t => 1 + size t 
  | Ite c t e => 1 + size c + size t + size e 
  | BinaryOp _ t1 t2 => 1 + size t1 + size t2
  | UnaryOp _ t => 1 + size t
  | Match s (_, lt) (_, rt) => 1 + size s + size lt + size rt
  end.