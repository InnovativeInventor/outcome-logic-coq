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

Lemma eq_set_respects_sat_atom S S' P :
  S ≡ S' ->
  S ⊨atom P ->
  S' ⊨atom P.
Proof.
  revert S S'. induction P; intros; solve_eq_set.
Qed.

Lemma eq_set_respects_sat S S' phi :
  S ≡ S' ->
  S ⊨ phi ->
  S' ⊨ phi.
Proof.
  revert S S'. induction phi; intros S S' Heq Hsat; simpgoal; eauto.
  - intros ?. split; intros. specialize (Heq x).
    specialize (Hsat x). simpgoal. solve_eq_set.
  - repeat eexists; intros; try eassumption.
    + apply H. apply Heq. assumption.
    + unfold "◇" in *. simpgoal.
      * solve_eq_set. apply Heq. apply H. left. assumption.
      * solve_eq_set. apply Heq. apply H. right. assumption.
  - apply Hsat; eauto with sets.
  - eapply eq_set_respects_sat_atom; eauto.
Qed.

Lemma null_implies_unmapped x S : S ⊨ x == null ⇒ (var x) -/->.
Proof.
  intros S' Heq Hsat. eapply eq_set_trans.
  - apply Hsat.
  - intros σ; split; intros; solve_eq_set.
    repeat eexists. eassumption.
Qed.

Lemma rule_zero_sound phi : ⊨ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩.
Proof.
  intros S ? σ. split.
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
  (forall S, S ⊨ phi' ⇒ phi) ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  (forall S, S ⊨ psi ⇒ psi') ->
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
  exists (S >>= ⟦ C1 ⟧). exists (S >>= ⟦ C2 ⟧).
  repeat split; intros; simpgoal'.
  - left. eauto.
  - right. eauto.
  - destruct H; simpgoal'.
    + repeat eexists. eauto using eval.
      apply EvalBr1. eassumption.
    + repeat eexists. eauto using eval.
      apply EvalBr2. eassumption.
Qed.

Lemma star_unfold C σ : ⟦ C ⋆ ⟧ σ ≡ ⟦ 𝟙 + C ⨟ C ⋆ ⟧ σ.
  intros σ'; split; intros H.
  - inversion H; simpgoal.
    + apply EvalBr1. constructor.
    + apply EvalBr2. assumption.
  - inversion H; clear H; simpgoal'. simpgoal.
Qed.

Lemma rule_induction_sound phi psi C :
  ⊨ ⟨ phi ⟩ 𝟙 + C ⨟ C ⋆ ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⋆ ⟨ psi ⟩.
Proof.
  intros H ? H'. eapply eq_set_respects_sat.
  2: { apply H. apply H'. }
  eapply cong_bind; intros; eauto with sets.
  apply eq_set_symm. apply star_unfold.
Qed.

Lemma rule_assign_sound x e :
  ⊨ ⟨ Ok ⟩ x <- e ⟨ x == e ⟩.
Proof. Admitted.

Lemma rule_alloc_sound x :
  ⊨ ⟨ Ok ⟩ x <- alloc ⟨ var x --> - ⟩.
Proof. Admitted.

Lemma rule_write_ok_sound e1 e2 :
  ⊨ ⟨ e1 --> - ⟩ [ e1 ] <- e2 ⟨ e1 --> e2 ⟩.
Proof. Admitted.

Lemma rule_write_err_sound e1 e2 :
  ⊨ ⟨ e1 -/-> ⟩ [ e1 ] <- e2 ⟨ Err ⟩.
Proof. Admitted.

Create HintDb atom_sound_lemmas.

Hint Resolve rule_assign_sound rule_alloc_sound rule_write_ok_sound
  rule_write_err_sound : atom_sound_lemmas.

Lemma rules_atom_sound P c Q :
  ⊢atom ⟨ P ⟩ c ⟨ Q ⟩ ->
  ⊨ ⟨ P ⟩ c ⟨ Q ⟩.
Proof. intros. induction H; eauto with atom_sound_lemmas. Qed.

Create HintDb sound_lemmas.

Hint Resolve rule_zero_sound rule_one_sound rule_seq_sound rule_split_sound
  rule_consequence_sound rule_empty_sound rule_true_sound rule_false_sound
  rule_plus_sound rule_induction_sound rules_atom_sound : sound_lemmas.

Theorem rules_sound phi C psi :
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof. intros. induction H; eauto with sound_lemmas. Qed.

Theorem semantic_falsification phi C psi :
  ((⊭sem ⟨ phi ⟩ C ⟨ psi ⟩))
      <->
  (exists phi',
    (phi' ⊆ phi) /\ (semantic_sat phi') /\ (semantic_triple phi' C (set_not psi ))).
Proof.
  split; intros.
  * unfold semantic_triple_neg in H.
    repeat destruct H.
    exists (ret x).
    split; try split.
    + unfold ret.
      unfold subseteq.
      intros.
      subst.
      apply H.
    + unfold semantic_sat.
      exists x.
      unfold ret.
      unfold member.
      auto.
    + unfold semantic_triple.
      intros.
      unfold member in *.
      unfold ret in *.
      subst.
      auto.
  * repeat destruct H.
    destruct H0.
    unfold semantic_sat in H0.
    destruct H0.
    unfold semantic_triple_neg.
    unfold semantic_triple in H1.
    exists x0.
    specialize (H x0 H0).
    split; auto.
Qed.
