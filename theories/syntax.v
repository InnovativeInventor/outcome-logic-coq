Unset Universe Checking.

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.Monads.StateMonad
     Data.List
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     Basics.CategoryKleisli
     Events.State
     Events.MapDefault.

From Coinduction Require Import all.

From CTree Require Import
     CTree
     Eq
     Misc.Pure
     Interp.Fold
     Interp.FoldCTree
     Interp.FoldStateT.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive expr : Type :=
| True
| False
.

Inductive cmd : Type :=
| assume : expr -> cmd
| assign : nat -> expr -> cmd
.

Inductive cl : Type :=
| Zero
| One
| Seq : cl -> cl -> cl
| Branch : cl -> cl -> cl
| Star : cl -> cl
| Atom : cmd -> cl
.

Inductive noop : Type -> Type :=
| tt : noop unit.

Notation computation := (ctree noop B02).

Definition state := nat -> expr.

Reserved Notation "[[ C ]]".

Fixpoint denote (C : cl) (st: state) : computation state :=
  match C with
  | Zero => Stuck
  | One => ret st
  | Seq C1 C2 => [[ C1 ]] st >>= [[ C2 ]]
  | Branch C1 C2 => br2 ([[ C1 ]] st) ([[ C2 ]] st)
  | Star C' =>
      iter (fun st' => br2
                         (st'' <-  [[ C' ]] st' ;; ret (inl st''))
                         (ret (inr st'))) st
  | _ => Stuck (* TODO *)
  end
where "[[ C ]]" := (denote C).
