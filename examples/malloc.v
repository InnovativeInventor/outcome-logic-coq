From OLCoq Require Import assertion metatheory ol rules semantics set syntax theorems util.

(* Program with a potential null dereference memory error *)
Example program x :=
      x <- malloc ⨟
      [ var x ] <- 1
.

(* Proof using outcome logic that the program may have a
   null dereference memory error *)
Example has_potential_memory_error x :
  ⊢ ⟨ ok ⟩ program x ⟨ var x --> 1 ⊕ Err ⟩.
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

(* Trace of program that leads to memory error, recovered from proof
   using outcome logic *)
Example error_witness x :
  (program x , empty_state) ⇓ err.
Proof.
  edestruct (rules_sound _ _ _ (has_potential_memory_error x))
    as [S [S' [H [_ Herr]]]].
  - exists empty_state. split.
    + eexists. eexists. reflexivity.
    + apply eq_set_refl.
  - specialize (H err) as [_ H].
    destruct H as [σ [Heq Heval]].
    + right. apply Herr. reflexivity.
    + rewrite Heq in *. apply Heval.
Qed.
