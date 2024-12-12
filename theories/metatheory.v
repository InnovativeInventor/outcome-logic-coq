Require Import semantics.
Require Import set.
Require Import ol.
Require Import util.

Ltac simp' :=
  match goal with
  | [ H : _ ∈ (fun _ => (𝟙, _) ⇓ _) |- _ ] =>
      inversion H; clear H
  | [ H : _ ∈ (fun _ => (_ ⨟ (_ ⋆), _) ⇓ _) |- _ ] =>
      idtac
  | [ H : _ ∈ (fun _ => (_ ⨟ _, _) ⇓ _) |- _ ] =>
      inversion H; clear H
  | [ H : _ ∈ (fun _ => (_ + _, _) ⇓ _) |- _ ] =>
      inversion H; clear H
  | [ H : _ ∈ (fun _ => (_ ⋆, _) ⇓ _) |- _ ] =>
      inversion H; clear H
  | [ H : _ ∈ (fun _ => (Atom _, _) ⇓ _) |- _ ] =>
      inversion H; clear H
  | [ H : (𝟙, _) ⇓ _ |- _ ] =>
      inversion H; clear H
  | [ H : (_ ⨟ (_ ⋆), _) ⇓ _ |- _ ] =>
      idtac
  | [ H : (_ ⨟ _, _) ⇓ _ |- _ ] =>
      inversion H; clear H
  | [ H : (_ + _, _) ⇓ _ |- _ ] =>
      inversion H; clear H
  | [ H : (_ ⋆, _) ⇓ _ |- _ ] =>
      inversion H; clear H
  | [ H : (Atom _, _) ⇓ _ |- _ ] =>
      inversion H; clear H
  | _ => simp
  end.

Ltac simpgoal' :=
  repeat (unfold bind, outputs, triple in *; simpl in *; simp').

Lemma eq_set_respects_sat s s' phi :
  s ≡ s' ->
  s ⊨ phi ->
  s' ⊨ phi.
Proof.
  revert s s'. induction phi; intros s s' Heq Hsat; simpgoal; eauto.
  - intros ?. split; intros. specialize (Heq x).
    specialize (Hsat x). simpgoal. solve_eq_set.
  - repeat eexists; intros; try eassumption.
    + apply H. apply Heq. assumption.
    + unfold "◇" in *. simpgoal.
      * solve_eq_set. apply Heq. apply H. left. assumption.
      * solve_eq_set. apply Heq. apply H. right. assumption.
  - apply Hsat; eauto with sets.
Qed.

Lemma rule_zero_sound phi : ⊨ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩.
Proof.
  intros s ? σ. split.
  - intros H'. destruct H' as [? [? Hc]]. inversion Hc.
  - intros Hc. inversion Hc.
Qed.

Lemma rule_one_sound phi : ⊨ ⟨ phi ⟩ 𝟙 ⟨ phi ⟩.
Proof.
  intros ? Hsat. eapply eq_set_respects_sat; try eassumption.
  split; intros H; repeat (simpgoal'; solve_eq_set).
Qed.

Lemma rule_seq_sound phi psi theta C1 C2 :
  ⊨ ⟨ phi ⟩ C1 ⟨ psi ⟩ ->
  ⊨ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
  ⊨ ⟨ phi ⟩ C1 ⨟ C2 ⟨ theta ⟩.
Proof.
  intros H1 H2 ??.
  eapply eq_set_respects_sat.
  2: { apply H2. apply H1. apply H. }
  split; intros; solve_eq_set; simpgoal'.
Qed.

Lemma rule_split_sound phi1 psi1 phi2 psi2 C :
  ⊨ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
  ⊨ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
  ⊨ ⟨ phi1 ⊕ phi2 ⟩ C ⟨ psi1 ⊕ psi2 ⟩.
Proof.
  intros H1 H2 ? [s1 [s2 [Heq [Hsat1 Hsat2]]]].
  exists (s1 >>= ⟦ C ⟧), (s2 >>= ⟦ C ⟧). repeat split; simpgoal.
  - destruct H as [? [Hin1 ?]]. apply Heq in Hin1. destruct Hin1.
    + left. repeat eexists; eassumption.
    + right. repeat eexists; eassumption.
  - destruct H as [H | H]; destruct H as [? [? ?]].
    + repeat eexists. apply Heq. left. all: eassumption.
    + repeat eexists. apply Heq. right. all: eassumption.
Qed.

Lemma rule_consequence_sound phi phi' psi psi' C :
  (forall s, s ⊨ phi' ⇒ phi) ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  (forall s, s ⊨ psi ⇒ psi') ->
  ⊨ ⟨ phi' ⟩ C ⟨ psi' ⟩.
Proof.
  intros H1 H H2 ? Hsat. eapply H2.
  - apply eq_set_refl.
  - apply H. eapply H1; try eassumption. apply eq_set_refl.
Qed.

Lemma rule_empty_sound C : ⊨ ⟨ ⊤⊕ ⟩ C ⟨ ⊤⊕ ⟩.
Proof.
  intros ? Hsat. eapply eq_set_respects_sat; try eassumption.
  intros ?. split; intros ?; simpgoal'.
  all: apply Hsat in H; destruct H.
Qed.

Lemma rule_true_sound phi C  : ⊨ ⟨ phi ⟩ C ⟨ ⊤ ⟩.
Proof. intros ??. constructor. Qed.

Lemma rule_false_sound C phi : ⊨ ⟨ ⊥ ⟩ C ⟨ phi ⟩.
Proof. intros ? Hc. destruct Hc. Qed.

Lemma rule_plus_sound phi psi1 psi2 C1 C2 :
  ⊨ ⟨ phi ⟩ C1 ⟨ psi1 ⟩ ->
  ⊨ ⟨ phi ⟩ C2 ⟨ psi2 ⟩ ->
  ⊨ ⟨ phi ⟩ C1 + C2 ⟨ psi1 ⊕ psi2 ⟩.
Proof.
  intros H1 H2. intros ? Hsat. simpl.
  exists (s >>= ⟦ C1 ⟧). exists (s >>= ⟦ C2 ⟧).
  repeat split; intros; simpgoal'.
  - left. eauto.
  - right. eauto.
  - destruct H; simpgoal'.
    + repeat eexists. eauto using eval.
      apply EvalBr1. eassumption.
    + repeat eexists. eauto using eval.
      apply EvalBr2. eassumption.
Qed.

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
