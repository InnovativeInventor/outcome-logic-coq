Require Import assertion metatheory ol rules semantics set util vec.

(* Soundness of outcome logic proof rules *)

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
  ⊨ ⟨ ok ⟩ x <- e ⟨ x == e ⟩.
Proof.
  intros ? [σ [[s [h Heq]] Hequ]].
  exists <{insert x (eval_expr e s) s, h}>. split; simpgoal.
  - repeat eexists. destruct e as [x' | |].
    all: simpgoal'; rewrite lookup_insert; eauto.
    unfold insert. destruct (string_dec x x'). all: eauto.
  - repeat eexists; intros; simpgoal'.
    + apply Hequ in H. simpgoal'.
    + apply Hequ. reflexivity.
    + eapply EvalCmd. eapply EvalAssign. eauto.
Qed.

Lemma rule_alloc_sound x :
  ⊨ ⟨ ok ⟩ x <- alloc ⟨ x --> - ⟩.
Proof.
  intros ? [σ [[s [h Heq]] Hequ]].
  destruct h as [n l].
  exists <{insert x (Some n) s , existT _ (Datatypes.S n) (append l None) }>.
  split.
  - destruct (find_le (append l None) n); try lia.
    repeat eexists.
    + unfold isnat. simpl. rewrite lookup_insert. reflexivity.
    + lia.
  - split; simpgoal'.
    + apply Hequ in H. simpgoal'.
    + repeat eexists.
      * apply Hequ. reflexivity.
      * eapply EvalCmd. eapply EvalAlloc; reflexivity.
Qed.

Lemma rule_store_ok_sound e1 e2 :
  ⊨ ⟨ e1 --> - ⟩ [ e1 ] <- e2 ⟨ e1 --> e2 ⟩.
Proof.
  intros ? [σ [[s [h [i [n [l H]]]]] Hequ]].
  remember (eval_expr e2 s) as v.
  destruct H as [? [Heq [H1 H2]]].
  exists <{s , existT _ n (update l i v)}>. split.
  - repeat eexists; try eassumption.
    unfold mapsto, load. rewrite find_update; eauto.
  - intros σ'; split; intros Hin.
    + destruct Hin as [σ'' [Hin1 Hin2]]. apply Hequ in Hin1.
      rewrite <- Hin1 in *. simpgoal'; unfold isnat in *;
        destruct (eval_expr e1 s); try contradiction; simpgoal.
    + rewrite <- Hin. repeat eexists; simpgoal.
      * eapply Hequ. reflexivity.
      * eapply EvalCmd. eapply EvalStore; simpgoal.
Qed.

Lemma rule_store_err_sound e1 e2 :
  ⊨ ⟨ e1 -/-> ⟩ [ e1 ] <- e2 ⟨ Err ⟩.
Proof.
  intros ? [σ [[s [h [Heq Heq']]] Hequ]].
  split; intros.
  - simpgoal'; eauto. apply Hequ in H. simpgoal'.
    unfold isnat in *. rewrite Heq' in *.
    contradiction.
  - repeat eexists.
    + apply Hequ. reflexivity.
    + simpgoal'. eapply EvalCmd.
      eapply EvalStoreNull. assumption.
Qed.

Lemma rule_load_ok_sound e e' x :
  ⊨ ⟨ e --> e' ⟩ x <- [ e ] ⟨ x == e' ⟩.
Proof.
  intros ? [σ [[s [h [i [v H]]]] Hequ]].
  destruct H as [Heq [H1 [Heq' H2]]]. simpgoal'.
  remember (eval_expr e' s) as v.
  exists <{ insert x v s , h }>.
  eexists. eexists. eexists. eexists.
  repeat split; try eauto.
  - destruct e' as [x'| |]; simpgoal'; rewrite lookup_insert; eauto.
    unfold insert. destruct (string_dec x x'). all: eauto.
  - intros σ'. split; intros H.
    + destruct H as [σ'' [Hin Heval]].
      apply Hequ in Hin. simpgoal'; unfold isnat, mapsto in *.
      * destruct (eval_expr e s); try contradiction. simpgoal'.
         destruct (load h n); try contradiction. simpgoal'.
      * destruct (eval_expr e s); try contradiction. simpgoal'.
    + repeat eexists; simpgoal'.
      * apply Hequ. reflexivity.
      * eapply EvalCmd. eapply EvalLoad; eauto.
Qed.

Lemma rule_load_err_sound e x :
  ⊨ ⟨ e -/-> ⟩ x <- [ e ] ⟨ error ⟩.
Proof.
  intros ? [σ [[s [h [Heq Heq']]] Hequ]].
  split; intros.
  - simpgoal'; eauto. apply Hequ in H. simpgoal'.
    unfold isnat in *. rewrite Heq' in *.
    contradiction.
  - repeat eexists.
    + apply Hequ. reflexivity.
    + simpgoal'. eapply EvalCmd.
      eapply EvalLoadNull. assumption.
Qed.

Create HintDb atom_sound_lemmas.

#[export] Hint Resolve rule_assign_sound rule_alloc_sound
  rule_store_ok_sound rule_store_err_sound rule_load_ok_sound
  rule_load_err_sound : atom_sound_lemmas.

Lemma rules_atom_sound P c Q :
  ⊢atom ⟨ P ⟩ c ⟨ Q ⟩ ->
  ⊨ ⟨ P ⟩ c ⟨ Q ⟩.
Proof. intros. induction H; eauto with atom_sound_lemmas. Qed.

Create HintDb sound_lemmas.

#[export] Hint Resolve rule_zero_sound rule_one_sound rule_seq_sound
  rule_split_sound rule_consequence_sound rule_empty_sound rule_true_sound
  rule_false_sound rule_plus_sound rule_induction_sound
  rules_atom_sound : sound_lemmas.
