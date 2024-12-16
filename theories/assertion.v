Require Import syntax.

(* Atomic assertions (propositions) for 'ok' states *)
Inductive okprop : Type :=
| OkTrue
| MapsTo (e : expr) (e : expr)
| Mapped (e : expr)
| Unmapped (e : expr)
| Assigned (x : nat) (e : expr)
.

Notation "'ok'" := OkTrue (at level 55).
Notation "e1 --> e2" := (MapsTo e1 e2) (at level 55).
Notation "e --> -" := (Mapped e) (at level 55).
Notation "e -/->" := (Unmapped e) (at level 55).
Notation "x == e" := (Assigned x e) (at level 55).

(* Atomic assertions (propositions) *)
Inductive prop : Type :=
| Ok : okprop -> prop
| Err : prop
.

Notation "'error'" := Err.

Coercion Ok : okprop >-> prop.

(* Outcome logic assertion language *)
Inductive assertion : Type :=
| Top : assertion
| Bot : assertion
| Diverge : assertion
| And : assertion -> assertion -> assertion
| Or : assertion -> assertion -> assertion
| Conj : assertion -> assertion -> assertion
| Impl : assertion -> assertion -> assertion
| Atomic : prop -> assertion
.

Coercion Atomic : prop >-> assertion.

Notation "⊤" := Top.
Notation "⊥" := Bot.
Notation "⊤⊕" := Diverge.
Notation "phi ∧ psi" := (And phi psi) (at level 70).
Notation "phi ∨ psi" := (Or phi psi) (at level 70).
Notation "phi ⊕ psi" := (Conj phi psi) (at level 80).
Notation "phi ⇒ psi" := (Impl phi psi) (at level 60).
