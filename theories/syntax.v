(* expressions *)
Inductive expr : Type :=
| Var : nat -> expr
| Tru : expr
| Fals : expr
.

(* atomic commands *)
Inductive cmd : Type :=
| assume : expr -> cmd
| assign : nat -> expr -> cmd
.

Notation "x <- e" := (assign x e) (at level 80).

(* command language *)
Inductive cl : Type :=
| Zero
| One
| Seq : cl -> cl -> cl
| Branch : cl -> cl -> cl
| Star : cl -> cl
| Atom : cmd -> cl
.

Coercion Atom : cmd >-> cl.

Notation "𝟘" := Zero.
Notation "𝟙" := One.
Notation "C ⋆" := (Star C) (at level 30).
Notation "C1 + C2" := (Branch C1 C2).
Notation "C1 ⨟ C2" := (Seq C1 C2) (at level 40).
