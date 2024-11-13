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
| Var : nat -> expr
| True : expr
| False : expr
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

Inductive weight : Type :=
| Bool : bool -> weight
| Unit : weight
.

Inductive noop : Type -> Type :=
| tt : noop unit.

Notation computation := (ctree noop B02).

Definition state := nat -> weight.

Reserved Notation "[[ c ]]".
Notation "x <<>> y" := (br2 x y) (at level 80).
Notation "[0]" := Stuck.

Definition insert (x : nat) (w : weight) (st : state) : state :=
  fun y => if Nat.eq_dec x y then w else st y.

Definition denote_expr (e : expr) (st: state) : weight :=
  match e with
    | Var x => st x
    | True => Bool true
    | False => Bool false
  end.


Definition test_weight (w : weight) : bool :=
  match w with
    | Bool b => b
    | Unit => false
  end.

Definition denote_cmd (c : cmd) (st: state) : computation state :=
  match c with
    | assume e => if test_weight (denote_expr e st) then ret st else [0]
    | assign x e => ret (insert x (denote_expr e st) st)
  end.

Fixpoint denote (C : cl) (st: state) : computation state :=
  match C with
  | Zero => [0]
  | One => ret st
  | Seq C1 C2 => [[ C1 ]] st >>= [[ C2 ]]
  | Branch C1 C2 => ([[ C1 ]] st) <<>> ([[ C2 ]] st)
  | Star C' =>
      iter (fun st' => (st'' <-  [[ C' ]] st' ;; ret (inl st''))
                         <<>>
                       (ret (inr st'))) st
  | Atom cmd => denote_cmd cmd st
  end
where "[[ C ]]" := (denote C).
Notation "x + y" := (Branch x y).
Notation "x ;;; y" := (Seq x y) (at level 80).

Theorem monoid_identity_l :
  forall (C : cl) (st: state) , [[ Zero + C ]] st ~ [[ C ]] st.
Proof.
  intros.
  apply br2_stuck_l.
Qed.

Theorem monoid_identity_r :
  forall (C : cl) (st: state) , [[ C + Zero ]] st ~ [[ C ]] st.
Proof.
  intros.
  apply br2_stuck_r.
Qed.

Theorem monoid_commutative :
    forall (C1 C2 : cl) (st: state) , [[ C1 + C2 ]] st ~ [[ C2 + C1 ]] st.
Proof.
  intros.
  apply br2_commut.
Qed.

Theorem monoid_respects_bind :
  forall (C1 C2 K : cl) (st : state), [[ (C1 + C2);;; K ]] st ~ [[ (C1;;; K) + (C2;;; K) ]] st.
Proof.
  intros.
  simpl.
Admitted.
