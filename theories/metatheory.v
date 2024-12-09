Unset Universe Checking.

Require Import semantics.
Require Import ol.
Require Import util.

Lemma sat_respects_sb m m' phi :
  m ~ m' ->
  m ⊨ phi ->
  m' ⊨ phi.
Proof.
  intros Hsb Hsat. revert m' Hsb.
  induction phi; intros; simpl in *; eauto.
  - rewrite <- Hsb. assumption.
  - destruct Hsat as [Hsat1 Hsat2]. split.
    + eapply IHphi1 in Hsat1; eassumption.
    + eapply IHphi2 in Hsat2; eassumption.
  - destruct Hsat as [Hsat1 | Hsat2].
    + left. eapply IHphi1 in Hsat1; eassumption.
    + right. eapply IHphi2 in Hsat2; eassumption.
  - destruct Hsat as [m1 [m2 [Hsb' [Hsat1 Hsat2]]]].
    repeat eexists. rewrite <- Hsb. all: eassumption.
  - intros m'' Hsb' Hsat1. apply Hsat.
    rewrite Hsb'. rewrite Hsb. reflexivity.
    assumption.
Qed.

Lemma sat_respects_equ m m' phi :
  m ≅ m' ->
  m ⊨ phi ->
  m' ⊨ phi.
Proof.
  intros.
  eapply sat_respects_sb.
  apply equ_sbisim_subrelation.
  apply eq_equivalence.
  all: eassumption.
Qed.

Lemma rule_zero_sound phi :
  ⊨ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩.
Proof.
  intros ??.
  (* maybe use is_stuck predicate here? *)
Admitted.

Lemma rule_one_sound phi :
  ⊨ ⟨ phi ⟩ 𝟙 ⟨ phi ⟩.
Proof.
  intros ??. simpl.
  eapply sat_respects_sb.
  - rewrite bind_ret_r. reflexivity.
  - eassumption.
Qed.

Theorem rules_sound phi C psi :
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof.
  intros. induction H.
  - apply rule_zero_sound.
  - apply rule_one_sound.
Admitted.
