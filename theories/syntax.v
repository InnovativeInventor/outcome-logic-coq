From Coq Require Export Strings.String.

(* Expressions: variables, literals, and null *)
Inductive expr : Type :=
| Var : string -> expr
| Lit : nat -> expr
| Null : expr
.

Notation "'null'" := Null.
Coercion Lit : nat >-> expr.
Coercion Var : string >-> expr.

(* Atomic commands: test expressions, read/write the stack/heap *)
Inductive cmd : Type :=
| Assume : expr -> cmd
| Not : expr -> cmd
| Assign : string -> expr -> cmd
| Alloc : string -> cmd
| Load : string -> expr -> cmd
| Store : expr -> expr -> cmd
.

Coercion Assume : expr >-> cmd.

Notation "¬ e" := (Not e) (at level 35).
Notation "x <- e" := (Assign x e) (at level 35).
Notation "[ e1 ] <- e2" := (Store e1 e2) (at level 35).
Notation "x <- [ e ]" := (Load x e) (at level 35).
Notation "x <- 'alloc'" := (Alloc x) (at level 35).

(* Command language: main language that programs are written in *)
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

(* Sugar for imperative programs *)

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
