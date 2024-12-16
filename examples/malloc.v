From OLCoq Require Import assertion lemmas ol rules semantics set syntax theorems util.

(* Program with a potential null dereference memory error *)
Example program x :=
      x <- malloc ⨟
      [ x ] <- 1
.

(* Proof using outcome logic that the program has two outcomes:
   1) successful store of value 1 to the pointer allocated to x
   2) memory error *)
Example spec x :
  ⊢ ⟨ ok ⟩ program x ⟨ x --> 1 ⊕ Err ⟩.
Proof.
  eapply RuleSeq.
  - eapply RulePlus.
    + eapply RuleCmd. eapply RuleAlloc.
    + eapply RuleCmd. eapply RuleAssign.
  - eapply RuleSplit; eauto using rules, rules_atom.
    eapply RuleConsequence.
    + apply null_implies_unmapped.
    + eapply RuleCmd. eapply RuleStoreErr.
    + intros ????. simpgoal.
Qed.

(* Trace of program that leads to successful store of 1 to the pointer
   allocated to x, recovered from proof using outcome logic *)
Example ok_witness x :
  exists s h i, (program x , empty_state) ⇓ <{s, h}> /\
                  isnat s x i /\ mapsto h i (Some 1).
Proof.
  edestruct (rules_sound _ _ _ (spec x))
    as [? [? [H [[σ [? Hequ]] _]]]].
  - exists empty_state. split.
    + eexists. eexists. reflexivity.
    + apply eq_set_refl.
  - specialize (H σ) as [_ H].
    destruct H as [? [Heq ?]].
    + left. apply Hequ. reflexivity.
    + rewrite Heq in *. simpgoal'.
      repeat eexists. all: eauto.
Qed.

(* Trace of program that leads to memory error, recovered from proof
   using outcome logic *)
Example error_witness x :
  (program x , empty_state) ⇓ err.
Proof.
  edestruct (rules_sound _ _ _ (spec x))
    as [? [? [H [_ Herr]]]].
  - exists empty_state. split.
    + eexists. eexists. reflexivity.
    + apply eq_set_refl.
  - specialize (H err) as [_ H].
    destruct H as [σ [Heq ?]].
    + right. apply Herr. reflexivity.
    + rewrite Heq in *. simpgoal.
Qed.
