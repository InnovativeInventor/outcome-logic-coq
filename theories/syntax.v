(* expressions *)
Inductive expr : Type :=
| Var : nat -> expr
| Lit : nat -> expr
| Null : expr
.

Notation "'var' x" := (Var x) (at level 30).
Notation "'null'" := Null.

Coercion Lit : nat >-> expr.

(* atomic commands *)
Inductive cmd : Type :=
| Assume : expr -> cmd
| Not : expr -> cmd
| Assign : nat -> expr -> cmd
| Alloc : nat -> cmd
| Read : nat -> expr -> cmd
| Write : expr -> expr -> cmd
.

Coercion Assume : expr >-> cmd.

Notation "¬ e" := (Not e) (at level 35).
Notation "x <- e" := (Assign x e) (at level 35).
Notation "[ e1 ] <- e2" := (Write e1 e2) (at level 35).
Notation "x <- [ e ]" := (Read x e) (at level 35).
Notation "x <- 'alloc'" := (Alloc x) (at level 35).

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
Notation "C ⋆" := (Star C) (at level 40).
Notation "C1 + C2" := (Branch C1 C2).
Notation "C1 ⨟ C2" := (Seq C1 C2) (at level 45).

(* sugar for imperative programs *)

Notation "x <- 'malloc'" := (x <- alloc + x <- null) (at level 35).

Notation "'skip'" := 𝟙.

Notation "'while' e 'do' C 'end'" := ((e ⨟ C) ⋆ ⨟ ¬ e).

Notation "'when' e 'then' C1 'otherwise' C2 'end'" :=
  ((e ⨟ C1) + (¬ e ⨟ C2)) (at level 50).

Fixpoint for_loop (n : nat) (C : cl) :=
  match n with
  | O => 𝟙
  | S n => C ⨟ for_loop n C
  end.

Notation "'for' n 'do' C 'end'" := (for_loop n C).

Declare Scope cl.
Delimit Scope cl with cl.
