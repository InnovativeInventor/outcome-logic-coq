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

Notation "𝟘" := Zero.
Notation "𝟙" := One.
Notation "C ⋆" := (Star C) (at level 60).
Notation "C1 + C2" := (Branch C1 C2).
Notation "C1 ⨟ C2" := (Seq C1 C2) (at level 80).

Inductive weight : Type :=
| Bool : bool -> weight
| Unit : weight
.

Inductive noop : Type -> Type :=
| tt : noop unit.

Notation M := (ctree noop B02).

Definition Σ := nat -> weight.

Definition insert (x : nat) (w : weight) (st : Σ) : Σ :=
  fun y => if Nat.eq_dec x y then w else st y.

Definition denote_expr (e : expr) (st: Σ) : weight :=
  match e with
  | Var x => st x
  | True => Bool true
  | False => Bool false
  end.

Definition weight_to_bool (w : weight) : bool :=
  match w with
  | Bool b => b
  | Unit => false
  end.

Notation "∅" := (Stuck : M Σ).

Definition denote_cmd (c : cmd) (st: Σ) : M Σ :=
  match c with
  | assume e =>
      if weight_to_bool (denote_expr e st) then ret st else ∅
  | assign x e => ret (insert x (denote_expr e st) st)
  end.

Reserved Notation "⟦ c ⟧".
Notation "x ◇ y" := (br2 x y) (at level 60).

Fixpoint denote (C : cl) (st : Σ) : M Σ :=
  match C with
  | 𝟘 => ∅
  | 𝟙 => ret st
  | C1 ⨟ C2 => ⟦ C1 ⟧ st >>= ⟦ C2 ⟧
  | C1 + C2 => (⟦ C1 ⟧ st) ◇ (⟦ C2 ⟧ st)
  | C ⋆ =>
      iter (fun st' => (st'' <-  ⟦ C ⟧ st' ;; ret (inl st''))
                         ◇
                       (ret (inr st'))) st
  | Atom cmd => denote_cmd cmd st
  end
where "⟦ C ⟧" := (denote C).

Theorem monoid_identity_l (m : M Σ) :
  ∅ ◇ m ~ m.
Proof.
  apply br2_stuck_l.
Qed.

Theorem monoid_identity_r (m : M Σ) :
  m ◇ ∅ ~ m.
Proof.
  apply br2_stuck_r.
Qed.

Theorem monoid_commutative (m1 m2 : M Σ) :
  m1 ◇ m2 ~ m2 ◇ m1.
Proof.
  intros.
  apply br2_commut.
Qed.

Theorem monoid_addition_preserves_bind {A : Type} (m1 m2 : M Σ)
  (k : Σ -> M Σ) :
  (m1 ◇ m2) >>= k ~ (m1 >>= k) ◇ (m2 >>= k).
Proof.
  intros. apply equ_sbisim_subrelation.
  - apply eq_equivalence.
  - simpl. unfold "◇". rewrite bind_br.
    apply br_equ. intros. destruct t; reflexivity.
Qed.

Print sb.

Theorem monoid_identity_cancels_bind {A : Type} (k : Σ -> M Σ) :
  ∅ >>= k ~ ∅.
Proof.
  intros. apply equ_sbisim_subrelation.
  - apply eq_equivalence.
  - apply bind_stuck.
Qed.
