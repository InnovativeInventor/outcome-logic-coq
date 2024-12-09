Unset Universe Checking.

Require Import semantics.
Require Import ol.
Require Import util.

Lemma sat_respects_sb m m' phi :
  m ~ m' ->
  m ⊨ phi ->
  m' ⊨ phi.
Proof.
Admitted.

Lemma sat_respects_equ m m' phi :
  m ≅ m' ->
  m ⊨ phi ->
  m' ⊨ phi.
Proof.
  intros.
  eapply sat_respects_sb.
  apply equ_sbisim_subrelation.
  apply eq_equivalence.
  apply H.
  apply H0.
Qed.

Lemma rule_zero_sound phi :
  ⊨ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩.
Proof.
  intros ??.
  unfold sat.
  apply equ_sbisim_subrelation.
  apply eq_equivalence.
  simpl.
  (* maybe use is_stuck predicate here? *)
Admitted.

Lemma rule_one_sound phi :
  ⊨ ⟨ phi ⟩ 𝟙 ⟨ phi ⟩.
Proof.
  intros ??. simpl.
  eapply sat_respects_sb.
  - admit.
  - eassumption.
Admitted.

Theorem rules_sound phi C psi :
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof.
  intros. induction H.
  - apply rule_zero_sound.
  - apply rule_one_sound.
Admitted.
