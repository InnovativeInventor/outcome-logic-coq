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

Definition value := nat.

Definition state := nat -> value.

(* TODO: concrete effect *)
Parameter effect : Type -> Type.

(* computation is a monad (>>= and ret already defined)  *
 * and a monoid                                          *)
Notation computation := (ctree effect B02).

(* monoid identity *)
Notation "∅" := (Stuck : computation state).
(* monoid addition *)
Notation "x ◇ y" := (br2 x y) (at level 60).
