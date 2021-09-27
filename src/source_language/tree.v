Require Import String List.

Inductive literal : Set := 
| IntLit (n: nat) 
| BoolLit (b: bool)
| UnitLit.

Inductive type : Set := 
| Int | Bool | Unit 
| Tuple (tpe1 tpe2: type) 
| Fun (args: list arg) (rettpe: type)
| ClassTpe (name: string)
with arg : Set := Arg (name: string) (tpe: type).

(* Unary and binary primitives are pure *)
Inductive binary_primitives : Set := 
| Add | Sub | Mul | Div | Mod 
| Lt | Lte | Eq 
| Or | And
| Tup.

Inductive unary_primitives : Set := 
| Neg | Not | Fst | Snd.

Inductive pattern : Set := 
| Wildcard | Lit (l: literal) 
| Id (name: string) | ClassConstr (name: string) (args: list arg).

Inductive term : Set := 
| Var (s: string)
| Const (l: literal)
| Let (x: arg) (t rest : term)
| LetRec (funs: list function) (rest : term)
| In 
| Out (t: term)
| Halt (t: term)
| Ite (cond thent elset: term)
| Seq (t1 t2: term)
| BinaryOp (op: binary_primitives) (t1 t2: term)
| UnaryOp (op: unary_primitives) (t: term)
| Match (scrut: term) (cases: list match_case)
| Constr (class_name: string) (args: list arg)
(* | NewRef (tpe: type) (t: term)
| UpdateRef (ref t: term)
| ReadRef (ref: term) *)
with 
  function : Set := Func (fname: string) (args: list arg) (rettpe: type) (body: term)
with
  match_case : Set := Case (p: pattern) (body: term).

Record class_def : Set := {class_name: string; args: list arg}.

Record class_tpe_def : Set := {tpe_name: string; class_defs: list class_def}.

Record program_def : Set := {class_tpe: list class_tpe_def; program: term}.