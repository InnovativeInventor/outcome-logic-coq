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
Proof. Admitted.

Lemma rule_split_sound phi1 psi1 phi2 psi2 C :
  ⊨ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
  ⊨ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
  ⊨ ⟨ phi1 ⊕ phi2 ⟩ C ⟨ psi1 ⊕ psi2 ⟩.
Proof. Admitted.

Lemma rule_consequence_sound phi phi' psi psi' C :
  (forall m, m ⊨ phi ⇒ phi') ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  (forall m, m ⊨ psi ⇒ psi') ->
  ⊨ ⟨ phi' ⟩ C ⟨ psi' ⟩.
Proof. Admitted.

Lemma rule_empty_sound C : ⊨ ⟨ ⊤⊕ ⟩ C ⟨ ⊤⊕ ⟩.
Proof. Admitted.

Lemma rule_true_sound phi C  : ⊨ ⟨ phi ⟩ C ⟨ ⊤ ⟩.
Proof. Admitted.

Lemma rule_false_sound C phi : ⊨ ⟨ ⊥ ⟩ C ⟨ phi ⟩.
Proof. Admitted.

Lemma rule_plus_sound phi psi1 psi2 C1 C2 :
  ⊨ ⟨ phi ⟩ C1 ⟨ psi1 ⟩ ->
  ⊨ ⟨ phi ⟩ C2 ⟨ psi2 ⟩ ->
  ⊨ ⟨ phi ⟩ C1 + C2 ⟨ psi1 ⊕ psi2 ⟩.
Proof. Admitted.

Lemma rule_induction_sound phi psi C :
  ⊨ ⟨ phi ⟩ 𝟙 + C ⨟ C ⋆ ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof. Admitted.

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
