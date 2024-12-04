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

(* expressions *)
Inductive expr : Type :=
| Var : nat -> expr
| Tru : expr
| Fals : expr
.

(* atomic commands *)
Inductive cmd : Type :=
| assume : expr -> cmd
| assign : nat -> expr -> cmd
.

(* command language *)
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

Inductive value : Type :=
| Bool : bool -> value
| Unit : value
.

Definition state := nat -> value.

Parameter effect : Type -> Type.

Notation computation := (ctree effect B02).

(* computation is a monad (>>= and ret already defined)
 * and a monoid *)

(* monoid identity *)
Notation "∅" := (Stuck : computation state).
(* monoid addition *)
Notation "x ◇ y" := (br2 x y) (at level 60).

Definition insert (x : nat) (w : value) (σ : state) : state :=
  fun y => if Nat.eq_dec x y then w else σ y.

Definition denote_expr (e : expr) (σ : state) : value :=
  match e with
  | Var x => σ x
  | Tru => Bool true
  | Fals => Bool false
  end.

Definition value_to_bool (v : value) : bool :=
  match v with
  | Bool b => b
  | Unit => false
  end.

Definition denote_cmd (c : cmd) (σ : state) : computation state :=
  match c with
  | assume e =>
      if value_to_bool (denote_expr e σ) then ret σ else ∅
  | assign x e =>
      ret (insert x (denote_expr e σ) σ)
  end.

Reserved Notation "⟦ c ⟧".

Fixpoint denote (C : cl) (σ : state) : computation state :=
  match C with
  | 𝟘 => ∅
  | 𝟙 => ret σ
  | C1 ⨟ C2 => ⟦ C1 ⟧ σ >>= ⟦ C2 ⟧
  | C1 + C2 => ⟦ C1 ⟧ σ ◇ ⟦ C2 ⟧ σ
  | C ⋆ =>
      iter (fun σ' =>
              (σ'' <-  ⟦ C ⟧ σ' ;; ret (inl σ''))
                ◇
                ret (inr σ')) σ
  | Atom cmd => denote_cmd cmd σ
  end
where "⟦ C ⟧" := (denote C).

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

Inductive assertion : Type :=
| Top : assertion
| Bot : assertion
| None : assertion
| And : assertion -> assertion -> assertion
| Or : assertion -> assertion -> assertion
| Conj : assertion -> assertion -> assertion
| Impl : assertion -> assertion -> assertion
| Atomic : Prop -> assertion
.

Notation "⊤" := Top.
Notation "⊥" := Bot.
Notation "⊤⊕" := None.
Notation "phi ∧ psi" := (And phi psi) (at level 80).
Notation "phi ∨ psi" := (Or phi psi) (at level 80).
Notation "phi ⊕ psi" := (Conj phi psi) (at level 80).
Notation "phi ⇒ psi" := (Impl phi psi) (at level 80).

Parameter sat_atom : computation state -> Prop -> Prop.

Reserved Notation "m ⊨ phi" (at level 80).

Fixpoint sat (m : computation state) (phi : assertion) : Prop :=
  match phi with
  | ⊤ => True
  | ⊥ => False
  | ⊤⊕ => m ≅ ∅
  | phi ∧ psi => m ⊨ phi /\ m ⊨ psi
  | phi ∨ psi => m ⊨ phi \/ m ⊨ psi
  | phi ⊕ psi => exists m1 m2, m ≅ m1 ◇ m2 /\ m1 ⊨ phi /\ m2 ⊨ psi
  | phi ⇒ psi => forall m', m' ≅ m -> m' ⊨ phi -> m' ⊨ psi
  | Atomic P => sat_atom m P
  end
where "m ⊨ phi" := (sat m phi).
