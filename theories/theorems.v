Require Import ol rules soundness.

(* Any derivable OL triple is semantically valid (i.e. given the precondition,
   any execution of the program results in the postcondition) *)
Theorem rules_sound phi C psi :
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  ⊨ ⟨ phi ⟩ C ⟨ psi ⟩.
Proof. intros. induction H; eauto with sound_lemmas. Qed.
