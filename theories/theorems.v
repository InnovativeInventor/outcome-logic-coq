Require Import ol rules soundness lemmas assertion set.

(* Any derivable OL triple is semantically valid (i.e. given the precondition,
   any execution of the program results in the postcondition) *)
Theorem rules_sound phi C psi :
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof. intros. induction H; eauto with sound_lemmas. Qed.

(* If a semantic triple ⟨ phi ⟩ C ⟨ psi ⟩ does not hold, there exists a superset
   phi' such that the negation of the triple holds. Note that we state a
   semantic triple *not* holding (⊭sem) constructively, meaning that there
   exists a countermodel to the triple. We restate the theorem constructively
   because the quantifier negation rules do not hold in our Coq encoding of sets.
   This is reasonable because:
       1) the theorem statements imply each other in ZF set theory
       2) all theorems we prove using the semantic falsification theorem hold
          without modification or are stronger (see principle of denial below).*)
Theorem semantic_falsification phi C psi :
  ((⊭sem ⟨ phi ⟩ C ⟨ psi ⟩))
      <->
  (exists phi',
    (phi' ⊆ phi) /\ (⊨sem phi') /\ (⊨sem ⟨ phi' ⟩  C ⟨ set_not psi ⟩)).
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

(* A syntactic triple holds iff the corresponding semantic interpretation holds. *)
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

(* If a precondition is ⟨ phi' ⟩ C ⟨ psi ⇒ ⊥ ⟩ holds and phi' is sat, then for
   any assertion phi weaker than phi', the triple ⟨ phi ⟩ C ⟨ psi ⟩ does not
   hold. Note that this is stronger than the principle of denial stated in the
   paper as it also provides a constructive witness to the syntatic triple
   ⟨ phi ⟩ C ⟨ psi ⟩ not holding. *)
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
