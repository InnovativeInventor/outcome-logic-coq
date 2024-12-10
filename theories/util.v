Unset Universe Checking.

Require Import computation.

Theorem monoid_identity_l (m : computation state) :
  ∅ ◇ m ~ m.
Proof.
  apply br2_stuck_l.
Qed.

Theorem monoid_identity_r (m : computation state) :
  m ◇ ∅ ~ m.
Proof.
  apply br2_stuck_r.
Qed.

Theorem monoid_commutative (m1 m2 : computation state) :
  m1 ◇ m2 ~ m2 ◇ m1.
Proof.
  intros.
  apply br2_commut.
Qed.

Theorem monoid_addition_preserves_bind (m1 m2 : computation state)
  (k : state -> computation state) :
  (m1 ◇ m2) >>= k ~ (m1 >>= k) ◇ (m2 >>= k).
Proof.
  intros. apply equ_sbisim_subrelation.
  - apply eq_equivalence.
  - simpl. unfold "◇". rewrite bind_br.
    apply br_equ. intros. destruct t; reflexivity.
Qed.

Theorem monoid_identity_cancels_bind (k : state -> computation state) :
  ∅ >>= k ~ ∅.
Proof.
  intros. apply equ_sbisim_subrelation.
  - apply eq_equivalence.
  - apply bind_stuck.
Qed.
