Unset Universe Checking.

Require Import computation.
Require Import semantics.

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
Notation "phi ∧ psi" := (And phi psi) (at level 60).
Notation "phi ∨ psi" := (Or phi psi) (at level 60).
Notation "phi ⊕ psi" := (Conj phi psi) (at level 60).
Notation "phi ⇒ psi" := (Impl phi psi) (at level 70).

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

Reserved Notation "⊢ ⟨ phi ⟩ C ⟨ psi ⟩".

Inductive rules : assertion -> cl -> assertion -> Prop :=
| RuleZero phi : ⊢ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩
| RuleOne phi : ⊢ ⟨ phi ⟩ 𝟙 ⟨ phi ⟩
| RuleSeq phi psi theta C1 C2 :
  ⊢ ⟨ phi ⟩ C1 ⟨ psi ⟩ ->
  ⊢ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
  ⊢ ⟨ phi ⟩ C1 ⨟ C2 ⟨ theta ⟩
| RuleSplit phi1 psi1 phi2 psi2 C :
  ⊢ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
  ⊢ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
  ⊢ ⟨ phi1 ⊕ phi2 ⟩ C ⟨ psi1 ⊕ psi2 ⟩
| RuleConsequence phi phi' psi psi' C :
  (forall m, m ⊨ phi' ⇒ phi) ->
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  (forall m, m ⊨ psi ⇒ psi') ->
  ⊢ ⟨ phi' ⟩ C ⟨ psi' ⟩
| RuleEmpty C : ⊢ ⟨ ⊤⊕ ⟩ C ⟨ ⊤⊕ ⟩
| RuleTrue phi C : ⊢ ⟨ phi ⟩ C ⟨ ⊤ ⟩
| RuleFalse C phi : ⊢ ⟨ ⊥ ⟩ C ⟨ phi ⟩
| RulePlus phi psi1 psi2 C1 C2 :
  ⊢ ⟨ phi ⟩ C1 ⟨ psi1 ⟩ ->
  ⊢ ⟨ phi ⟩ C2 ⟨ psi2 ⟩ ->
  ⊢ ⟨ phi ⟩ C1 + C2 ⟨ psi1 ⊕ psi2 ⟩
| RuleInduction phi psi C :
  ⊢ ⟨ phi ⟩ 𝟙 + C ⨟ C ⋆ ⟨ psi ⟩ ->
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩
where "⊢ ⟨ phi ⟩ C ⟨ psi ⟩" := (rules phi C psi).
