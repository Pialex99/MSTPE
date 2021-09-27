CoInductive stream : Set :=
| Cons (h: nat) (t: stream)
| Nil.