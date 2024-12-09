Unset Universe Checking.

From Coq Require Export
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Unset Universe Checking.

From ExtLib Require Export 
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.Monads.StateMonad
     Data.List
     Data.Map.FMapAList.

From ITree Require Export 
     ITree
     Basics.CategoryKleisli
     Events.State
     Events.MapDefault.

From Coinduction Require Export all.

From CTree Require Export 
     CTree
     Eq
     Misc.Pure
     Interp.Fold
     Interp.FoldCTree
     Interp.FoldStateT.

Export ListNotations.
Export MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

Inductive value : Type :=
| Bool : bool -> value
| Unit : value
.

Definition state := nat -> value.

(* TODO: use a concrete effect *)
Parameter effect : Type -> Type.

(* computation is a monad (>>= and ret already defined)  *
 * and a monoid                                          *)
Notation computation := (ctree effect B02).

(* monoid identity *)
Notation "∅" := (Stuck : computation state).
(* monoid addition *)
Notation "x ◇ y" := (br2 x y) (at level 60).

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
