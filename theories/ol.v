Require Import assertion.
Require Import semantics.
Require Import set.
Require Import vec.

(* Satisfiability of a proposition for an 'ok' state *)
Definition sat_state (σ : state) (P : okprop) : Prop :=
  match P with
  | OkTrue => exists s h, σ = <{s , h}>
  | e1 --> e2 =>
      exists s h i v,
        σ = <{s, h}> /\ isnat s e1 i /\ eval_expr e2 s = v /\ mapsto h i v
  | e --> - =>
      exists s h i n (l : vec n value), σ = <{s, h}> /\ h = existT _ n l /\ isnat s e i /\ i < n
  | e -/-> => exists s h, σ = <{s, h}> /\ eval_expr e s = None
  | x == e =>
      exists s h v, σ = <{s, h}> /\ eval_expr e s = v /\ eval_expr x s = v
  end.

Notation "σ ⊨state P" := (sat_state σ P) (at level 80).

(* Satisfiability of propositions *)
Definition sat_atom (S : set state) (P : prop) : Prop :=
  match P with
  | Err => S ≡ ret err
  | Ok P => exists σ, σ ⊨state P /\ S ≡ ret σ
  end.

Notation "S ⊨atom P" := (sat_atom S P) (at level 80).

Reserved Notation "S ⊨ phi" (at level 80).

(* Satisfiability of assertions *)
Fixpoint sat (S : set state) (phi : assertion) : Prop :=
  match phi with
  | ⊤ => True
  | ⊥ => False
  | ⊤⊕ => S ≡ ∅
  | phi ∧ psi => S ⊨ phi /\ S ⊨ psi
  | phi ∨ psi => S ⊨ phi \/ S ⊨ psi
  | phi ⊕ psi => exists S1 S2, S ≡ S1 ◇ S2 /\ S1 ⊨ phi /\ S2 ⊨ psi
  | phi ⇒ psi => forall S', S ≡ S' -> S' ⊨ phi -> S' ⊨ psi
  | Atomic P => S ⊨atom P
  end
where "S ⊨ phi" := (sat S phi).

(* Set of possible states reachable from a program and a given state *)
Definition outputs (C : cl) (σ : state) : set state :=
  fun σ' => (C , σ) ⇓ σ'.

Notation "⟦ C ⟧" := (outputs C).

(* Outcome logic triple *)
Definition triple (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  forall S, S ⊨ phi -> (S >>= ⟦ C ⟧) ⊨ psi.

Notation "⊨ ⟨ phi ⟩ C ⟨ psi ⟩" := (triple phi C psi).

Definition triple_neg (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  exists S, S ⊨ phi /\ ~ ((S >>= ⟦ C ⟧) ⊨ psi).

Notation "⊭ ⟨ phi ⟩ C ⟨ psi ⟩" := (triple_neg phi C psi).

Definition semantic_interpretation (phi : assertion) : set (set state) :=
  fun x => sat x phi.

Definition semantic_triple (phi : set (set state)) (C : cl) (psi : set (set state)) : Prop :=
  forall m, m ∈ phi -> (m >>= ⟦ C ⟧) ∈ psi.

Notation "⊨sem ⟨ phi ⟩ C ⟨ psi ⟩" := (semantic_triple phi C psi) (at level 90).

Definition semantic_sat (phi : set (set state)) : Prop :=
  exists x, x ∈ phi.

Notation "⊨sem phi" := (semantic_sat phi) (at level 80).

Definition semantic_triple_neg (phi : set (set state)) (C : cl) (psi : set (set state)) : Prop :=
  exists m, m ∈ phi /\ (m >>= ⟦ C ⟧) ∈ (set_not psi).

Notation "⊭sem ⟨ phi ⟩ C ⟨ psi ⟩" := (semantic_triple_neg phi C psi).

(* Underapproximation triple *)
Definition underapprox (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  triple phi C (psi ⊕ ⊤).

Notation "⊨↓ ⟨ phi ⟩ C ⟨ psi ⟩" := (underapprox phi C psi).

(* Partial correctness triple *)
Definition pc (phi : assertion) (C : cl) (psi : assertion) : Prop :=
  triple phi C (psi ⊕ ⊤⊕).

Notation "⊨pc ⟨ phi ⟩ C ⟨ psi ⟩" := (pc phi C psi).
