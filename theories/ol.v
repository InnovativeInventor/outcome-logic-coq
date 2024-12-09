Unset Universe Checking.

Require Import semantics.
Require Import util.

Inductive prop : Type :=
| Sat
| Unsat
.

Inductive assertion : Type :=
| Top : assertion
| Bot : assertion
| None : assertion
| And : assertion -> assertion -> assertion
| Or : assertion -> assertion -> assertion
| Conj : assertion -> assertion -> assertion
| Impl : assertion -> assertion -> assertion
| Atomic : prop -> assertion
.

Coercion Atomic : prop >-> assertion.

Notation "⊤" := Top.
Notation "⊥" := Bot.
Notation "⊤⊕" := None.
Notation "phi ∧ psi" := (And phi psi) (at level 80).
Notation "phi ∨ psi" := (Or phi psi) (at level 80).
Notation "phi ⊕ psi" := (Conj phi psi) (at level 80).
Notation "phi ⇒ psi" := (Impl phi psi) (at level 80).

(* TODO: add more atomic propositions *)
Definition sat_atom (m : computation state) (P : prop) : Prop :=
  match P with
  | Sat => True
  | Unsat => False
  end.

Reserved Notation "m ⊨ phi" (at level 80).

Fixpoint sat (m : computation state) (phi : assertion) : Prop :=
  match phi with
  | ⊤ => True
  | ⊥ => False
  | ⊤⊕ => m ~ ∅
  | phi ∧ psi => m ⊨ phi /\ m ⊨ psi
  | phi ∨ psi => m ⊨ phi \/ m ⊨ psi
  | phi ⊕ psi => exists m1 m2, m ~ m1 ◇ m2 /\ m1 ⊨ phi /\ m2 ⊨ psi
  | phi ⇒ psi => forall m', m' ~ m -> m' ⊨ phi -> m' ⊨ psi
  | Atomic P => sat_atom m P
  end
where "m ⊨ phi" := (sat m phi).

Definition triple (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  forall (m : computation state), m ⊨ phi -> (m >>= ⟦ C ⟧) ⊨ psi.

Notation "⊨ ⟨ phi ⟩ C ⟨ psi ⟩" := (triple phi C psi).

Definition underapprox (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  triple phi C (psi ⊕ ⊤).

Notation "⊨↓ ⟨ phi ⟩ C ⟨ psi ⟩" := (underapprox phi C psi).

Definition pc (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  triple phi C (psi ⊕ ⊤⊕).

Notation "⊨pc ⟨ phi ⟩ C ⟨ psi ⟩" := (pc phi C psi).

Example ex : ⊨ ⟨ ⊤ ⟩ assume Tru ⟨ ⊤ ⟩.
Proof.
  intros ??. constructor.
Qed.

Reserved Notation "⊢ ⟨ phi ⟩ C ⟨ psi ⟩".

Inductive rules : assertion -> cl -> assertion -> Prop :=
| RuleZero : forall phi, rules phi 𝟘 ⊤⊕
| RuleOne : forall phi, rules phi 𝟙 phi
where "⊢ ⟨ phi ⟩ C ⟨ psi ⟩" := (rules phi C psi).
