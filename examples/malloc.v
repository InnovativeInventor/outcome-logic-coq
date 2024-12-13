From OLCoq Require Import syntax ol metatheory util set.

Definition buggy_program (x : nat) : cl :=
  x <- malloc ⨟
  [ var x ] <- 1
.

Theorem spec x : ⊢ ⟨ Ok ⟩ buggy_program x ⟨ var x --> 1 ⊕ Err ⟩.
Proof. Admitted.
