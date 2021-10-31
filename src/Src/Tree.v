From Utils Require Export Int.

Inductive literal : Set := 
| IntLit (n: int) 
| BoolLit (b: bool)
| UnitLit.

Definition lit_eqb l1 l2 :=
  match l1, l2 with
  | IntLit n1, IntLit n2 => BinIntDef.Z.eqb n1 n2
  | BoolLit b1, BoolLit b2 => Bool.eqb b1 b2
  | UnitLit, UnitLit => true
  | _, _ => false
  end.

(* Inductive type : Set := 
| Int | Bool | Unit 
| Tuple (tpe1 tpe2: type) 
| Fun (args: list type) (rettpe: type)
| Sum (ltpe rtpe : type). *)

(* Record arg : Set := {name: nat;tpe: type}. *)

(* Unary and binary primitives are pure *)
Inductive binary_primitives : Set := 
| Add | Sub | Mul | Div | Mod 
| Lt | Le | Eq
| Or | And
| Tup.

Inductive unary_primitives : Set := 
| Neg | Not | Fst | Snd | Left | Right.

Inductive term : Set := 
| Var (n: nat)
| Const (l: literal)
| Let (x: nat) (t rest : term)
(* | Let (x: arg) (t rest : term) *)
(* | LetRec (funs: list function) (rest : term) *)
| LetRec (f: function) (rest : term)
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
  function : Set := Func (fname: nat) (arg: nat) (body: term).
  (* function : Set := Func (fname: nat) (args: list arg) (rettpe: type) (body: term). *)
