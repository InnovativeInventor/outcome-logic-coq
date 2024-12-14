From OLCoq Require Import syntax ol metatheory util set.

Definition buggy_program (x : nat) : cl :=
  x <- malloc ⨟
  [ var x ] <- 1
.

Theorem spec x : ⊢ ⟨ ok ⟩ buggy_program x ⟨ var x --> 1 ⊕ Err ⟩.
Proof.
  eapply RuleSeq.
  - eapply RulePlus.
    + eapply RuleCmd. eapply RuleAlloc.
    + eapply RuleCmd. eapply RuleAssign.
  - eapply RuleSplit; eauto using rules, rules_atom.
    eapply RuleConsequence. 2: { eapply RuleCmd. eapply RuleWriteErr. }
    + apply null_implies_unmapped.
    + intros ????. solve_eq_set.
Qed.
