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

Lemma syntactic_to_semantic_triples phi C psi phi_sem psi_sem :
  (phi_sem = semantic_interpretation phi /\
      psi_sem = semantic_interpretation psi) ->
  ((⊨sem ⟨ phi_sem ⟩ C ⟨ psi_sem ⟩) <-> (⊨ ⟨ phi ⟩ C ⟨ psi ⟩)).
Proof.
  split.
  * destruct H. intros.
    unfold semantic_triple in *.
    unfold triple in *.
    intros.
    specialize (H1 S).
    assert (S ∈ phi_sem).
    {
      unfold member.
      rewrite H.
      unfold semantic_interpretation.
      apply H2.
    }
    specialize (H1 H3).
    unfold member in H1.
    rewrite H0 in H1.
    unfold semantic_interpretation in H1.
    apply H1.
  * intros.
    destruct H.
    unfold semantic_triple.
    intros.
    subst.
    unfold triple in H0.
    specialize (H0 m H2).
    apply H0.
Qed.

Lemma syntactic_to_semantic_triples_neg phi C psi phi_sem psi_sem :
  (phi_sem = semantic_interpretation phi /\
      psi_sem = semantic_interpretation psi) ->
  ((⊭sem ⟨ phi_sem ⟩ C ⟨ psi_sem ⟩) <-> (⊭ ⟨ phi ⟩ C ⟨ psi ⟩)).
Proof.
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


(* Check semantic_interpretation. *)
(* Definition extensional_equiv (f g : set (set state)) := *)
(*   forall a, f a = g a. *)
(* not sure how to use \equiv notation here*)

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

Theorem principle_of_denial phi phi' C psi :
  ((forall m, (m ⊨ phi') -> (m ⊨ phi)) /\
    exists m, m ⊨ phi' /\
    ⊨ ⟨ phi' ⟩ C ⟨ psi ⇒ ⊥ ⟩ ) ->
  ⊭  ⟨ phi ⟩ C ⟨ psi ⟩.
Proof.
  intros.
  destruct H.
  repeat destruct H0.
  epose proof (H _ H0).
  remember (semantic_interpretation phi) as phi_sem.
  remember (semantic_interpretation phi') as phi'_sem.
  remember (semantic_interpretation psi) as psi_sem.
  eapply (syntactic_to_semantic_triples_neg _ C _ phi_sem psi_sem); auto.
  eapply (semantic_falsification phi_sem C psi_sem).
  exists phi'_sem.
  subst.
  split.
  * unfold subseteq.
    intros.
    unfold semantic_interpretation in *.
    auto.
  * split.
    - exists x.
      auto.
    - eapply (syntactic_to_semantic_triples_ext phi' C (psi ⇒ ⊥) (semantic_interpretation phi') (set_not (semantic_interpretation psi))).
      + split; auto.
        ++ unfold set_not.
           unfold semantic_interpretation.
           unfold not.
           unfold eq_set.
           intros.
           split;auto.
        ++ unfold semantic_interpretation.
           unfold set_not.
           simpl.
           unfold eq_set.
           split.
           +++ intros.
               apply H3.
               apply (eq_set_respects_sat S' x0).
               split; apply H4.
               apply H5.
           +++ intros.
               unfold not.
               intros.
               apply (H3 x0).
               intros.
               split; auto.
               apply H4.
      + apply H1.
Qed.
