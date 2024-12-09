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

Lemma rule_zero_sound phi :
  ⊨ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩.
Proof.
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
