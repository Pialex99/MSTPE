(* Unary and binary primitives are pure *)
Inductive binary_primitives : Set := 
| Add | Sub | Mul | Div | Mod 
| Lt | Le | Eq
| Or | And
| Tup.

Inductive unary_primitives : Set := 
| Neg | Not | Fst | Snd | Left | Right | Id.