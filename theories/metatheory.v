Unset Universe Checking.

Require Import computation.
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

Lemma rule_zero_sound phi : ⊨ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩.
Proof.
  intros ??.
  (* maybe use is_stuck predicate here? *)
Admitted.

Lemma rule_one_sound phi : ⊨ ⟨ phi ⟩ 𝟙 ⟨ phi ⟩.
Proof.
  intros ??. simpl.
  eapply sat_respects_sb.
  - rewrite bind_ret_r. reflexivity.
  - eassumption.
Qed.

Lemma rule_seq_sound phi psi theta C1 C2 :
  ⊨ ⟨ phi ⟩ C1 ⟨ psi ⟩ ->
  ⊨ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
  ⊨ ⟨ phi ⟩ C1 ⨟ C2 ⟨ theta ⟩.
Proof.
  intros H1 H2 ? Hsat.
  eapply sat_respects_sb.
  - simpl. rewrite <- bind_bind. reflexivity.
  - specialize (H1 _ Hsat). specialize (H2 _ H1). assumption.
Qed.

Lemma rule_split_sound phi1 psi1 phi2 psi2 C :
  ⊨ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
  ⊨ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
  ⊨ ⟨ phi1 ⊕ phi2 ⟩ C ⟨ psi1 ⊕ psi2 ⟩.
Proof.
  intros H1 H2 m [m1 [m2 [Hsb [Hsat1 Hsat2]]]].
  specialize (H1 _ Hsat1). specialize (H2 _ Hsat2).
  repeat eexists; try eassumption.
  rewrite Hsb. apply monoid_addition_preserves_bind.
Qed.

Lemma rule_consequence_sound phi phi' psi psi' C :
  (forall m, m ⊨ phi' ⇒ phi) ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  (forall m, m ⊨ psi ⇒ psi') ->
  ⊨ ⟨ phi' ⟩ C ⟨ psi' ⟩.
Proof.
  intros H1 H H2 ? Hsat. simpl in H1, H2.
  eapply H1 in Hsat; eauto.
Qed.

Lemma rule_empty_sound C : ⊨ ⟨ ⊤⊕ ⟩ C ⟨ ⊤⊕ ⟩.
Proof.
  intros.
  unfold triple.
  intros.
  unfold sat in *.
  simpl.
  assert (is_stuck m).
  rewrite H.
  apply Stuck_is_stuck.
  assert (is_stuck (CTree.bind m ⟦ C ⟧)).
  apply is_stuck_bind.
  apply H0.
  epose proof (Stuck_is_stuck).
  epose proof (is_stuck_sb (sbisim _) H1 H2).
  erewrite H3.
  auto.
Qed.

Lemma rule_true_sound phi C  : ⊨ ⟨ phi ⟩ C ⟨ ⊤ ⟩.
Proof. intros ??. constructor. Qed.

Lemma rule_false_sound C phi : ⊨ ⟨ ⊥ ⟩ C ⟨ phi ⟩.
Proof. intros ??. inversion H. Qed.

Lemma rule_plus_sound phi psi1 psi2 C1 C2 :
  ⊨ ⟨ phi ⟩ C1 ⟨ psi1 ⟩ ->
  ⊨ ⟨ phi ⟩ C2 ⟨ psi2 ⟩ ->
  ⊨ ⟨ phi ⟩ C1 + C2 ⟨ psi1 ⊕ psi2 ⟩.
Proof.
  intros H1 H2 ? Hsat.
  specialize (H1 _ Hsat). specialize (H2 _ Hsat).
  simpl. repeat eexists; try eassumption.
  (* TODO: is this goal true *)
Admitted.

Lemma rule_induction_sound phi psi C :
  ⊨ ⟨ phi ⟩ 𝟙 + C ⨟ C ⋆ ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof.
  intros H ? Hsat.
  specialize (H _ Hsat).
  (* TODO: this is the hard one... *)
Admitted.

Create HintDb sound_lemmas.

Hint Resolve rule_zero_sound rule_one_sound rule_seq_sound rule_split_sound
  rule_consequence_sound rule_empty_sound rule_true_sound rule_false_sound
  rule_plus_sound rule_induction_sound : sound_lemmas.

Theorem rules_sound phi C psi :
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof.
  intros. induction H; eauto with sound_lemmas.
Qed.
