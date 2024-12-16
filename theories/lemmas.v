Require Import assertion.
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
  | [ H : eval_cmd (Assume _) _ _ |- _ ] =>
      inversion H; clear H
  | [ H : eval_cmd (¬ _) _ _ |- _ ] =>
      inversion H; clear H
  | [ H : eval_cmd (_ <- alloc) _ _ |- _ ] =>
      inversion H; clear H
  | [ H : eval_cmd (_ <- _) _ _ |- _ ] =>
      inversion H; clear H
  | [ H : eval_cmd ([ _ ] <- _) _ _ |- _ ] =>
      inversion H; clear H
  | [ H : eval_cmd (_ <- [ _ ]) _ _ |- _ ] =>
      inversion H; clear H
  | [ H : <{ _ , _ }> = <{ _ , _ }> |- _ ] =>
      inversion H; clear H
  | _ => simp
  end.

Ltac simpgoal' :=
  repeat (unfold bind, outputs, triple, ret in *; simpl in *; simp').

Lemma eq_set_respects_sat_atom S S' P :
  S ≡ S' ->
  S ⊨atom P ->
  S' ⊨atom P.
Proof.
  revert S S'. induction P; simpl in *; intros; simpgoal.
  - repeat eexists; try eassumption.
    + intros Hin. apply H1. apply H. apply Hin.
    + intros Hin. apply H. apply H1. apply Hin.
  - repeat eexists.
    + intros Hin. apply H0. apply H. apply Hin.
    + intros Hin. apply H. apply H0. apply Hin.
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

Lemma null_implies_unmapped x S : S ⊨ x == null ⇒ x -/->.
Proof.
  intros S' Heq [σ [Hin Hsat]]. unfold sat, sat_atom, sat_state in *.
  exists σ. split.
  - simpgoal'. repeat eexists. eauto.
  - simpgoal'. repeat eexists.
    + intros Hin. apply Hsat. apply Hin.
    + intros Hin. apply Hsat. apply Hin.
Qed.

Lemma syntactic_to_semantic_triples_neg phi C psi phi_sem psi_sem :
  (phi_sem = semantic_interpretation phi /\
      psi_sem = semantic_interpretation psi) ->
  ((⊭sem ⟨ phi_sem ⟩ C ⟨ psi_sem ⟩) <-> (⊭ ⟨ phi ⟩ C ⟨ psi ⟩)).
Proof.
  intros.
  split.
  * destruct H. intros.
    unfold semantic_triple_neg in *.
    unfold triple_neg in *.
    destruct H1.
    exists x.
    destruct H1.
    subst.
    unfold semantic_interpretation in *.
    split; auto.
  * destruct H. intros.
    unfold semantic_triple_neg in *.
    unfold triple_neg in *.
    destruct H1.
    exists x.
    destruct H1.
    subst.
    unfold semantic_interpretation in *.
    split; auto.
Defined.

Lemma syntactic_to_semantic_triples_ext phi C psi phi_sem psi_sem :
  ((phi_sem ≡ (semantic_interpretation phi)) /\
      (psi_sem ≡ (semantic_interpretation psi))) ->
  ((⊨sem ⟨ phi_sem ⟩ C ⟨ psi_sem ⟩) <-> (⊨ ⟨ phi ⟩ C ⟨ psi ⟩)).
Proof.
  split.
  * destruct H. intros.
    unfold semantic_triple in *.
    unfold triple in *.
    intros.
    specialize (H1 S).
    unfold eq_set in *.
    assert (S ∈ phi_sem).
    {
      unfold member.
      eapply H.
      unfold semantic_interpretation.
      apply H2.
    }
    specialize (H1 H3).
    unfold member in H1.
    erewrite H0 in H1.
    unfold semantic_interpretation in H1.
    apply H1.
  * intros.
    destruct H.
    unfold semantic_triple.
    intros.
    subst.
    unfold triple in H0.
    unfold eq_set in *.
    specialize (H0 m).
    unfold member in *.
    erewrite H1.
    erewrite H in H2.
    unfold semantic_interpretation in *.
    apply H0.
    apply H2.
Qed.
(* the above few proofs can probably be simplified *)

