Require Import semantics.
Require Import set.

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
Definition sat_atom (s : set state) (P : prop) : Prop :=
  match P with
  | Sat => True
  | Unsat => False
  end.

Reserved Notation "s ⊨ phi" (at level 80).

Fixpoint sat (s : set state) (phi : assertion) : Prop :=
  match phi with
  | ⊤ => True
  | ⊥ => False
  | ⊤⊕ => s ≡ ∅
  | phi ∧ psi => s ⊨ phi /\ s ⊨ psi
  | phi ∨ psi => s ⊨ phi \/ s ⊨ psi
  | phi ⊕ psi => exists s1 s2, s ≡ s1 ◇ s2 /\ s ⊨ phi /\ s ⊨ psi
  | phi ⇒ psi => forall s', s ≡ s' -> s ⊨ phi -> s ⊨ psi
  | Atomic P => sat_atom s P
  end
where "m ⊨ phi" := (sat m phi).

Definition outputs (C : cl) (σ : state) : set state :=
  fun σ' => (C , σ) ⇓ σ'.

Notation "⟦ C ⟧" := (outputs C).

Definition triple (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  forall s, s ⊨ phi -> (s >>= ⟦ C ⟧) ⊨ psi.

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
