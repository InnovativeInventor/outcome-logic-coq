Require Import util.

(* Set library *)

Definition set (X : Type) := X -> Prop.

Definition eq_set `{X : Type} (S1 : set X) (S2 : set X) : Prop :=
  forall x, S1 x <-> S2 x.

Notation "S1 ≡ S2" := (eq_set S1 S2) (at level 80).

Definition empty `{X : Type} : set X :=
  fun _ => False.

Definition member `{X : Type} (x : X) (S : set X) := S x.

Notation "x ∈ S" := (member x S) (at level 80).

Notation "∅" := empty.

Definition union `{X : Type} (S1 : set X) (S2 : set X) : set X :=
  fun x => S1 x \/ S2 x.

Notation "S1 ◇ S2" := (union S1 S2) (at level 70).

Definition set_not `{X : Type} (S : set X) : set X := fun x => ~ S x.

Notation "¬set S" := (not S) (at level 70).

Definition subseteq `{X : Type} (S1 : set X) (S2 : set X) : Prop :=
  forall x, S1 x -> S2 x.

Notation "S1 ⊆ S2" := (subseteq S1 S2) (at level 70).

Definition ret `{X : Type} (x : X) : set X :=
  fun x' => x = x'.

Definition bind `{X : Type} (S : set X) (f : X -> set X) : set X :=
  fun x => exists x', x' ∈ S /\ x ∈ f x'.

Notation "s >>= f" := (bind s f) (at level 70).

Ltac simp_eq_set_goal := unfold ret, "∅", "∈", "◇", bind, "≡" in *; simpgoal.

Ltac solve_eq_set_base:= repeat (progress simp_eq_set_goal).

Lemma eq_set_refl `{X : Type} (S : set X) : S ≡ S.
Proof.
  intros ?. split; intros ?; solve_eq_set_base.
Qed.

Lemma eq_set_trans `{X : Type} (S1 S2 S3 : set X) :
  S1 ≡ S2 ->
  S2 ≡ S3 ->
  S1 ≡ S3.
Proof.
  intros Heq1 Heq2 ?. split; intros ?; solve_eq_set_base.
  all: specialize (Heq1 x); specialize (Heq2 x); simpgoal.
Qed.

Lemma eq_set_symm `{X : Type} (S1 S2 : set X) :
  S1 ≡ S2 ->
  S2 ≡ S1.
Proof.
  intros Heq ?. split; intros ?; solve_eq_set_base.
  all: specialize (Heq x); solve_eq_set_base.
Qed.

Lemma bind_ret_r `{X : Type} (S : set X) : (S >>= ret) ≡ S.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma bind_ret_l `{X : Type} (x : X) f : (ret x >>= f) ≡ f x.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.
    
Lemma bind_assoc `{X : Type} (S : set X) f g :
  (S >>= f) >>= g ≡ S >>= (fun x => f x >>= g).
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma union_comm `{X : Type} (S1 S2 : set X) : S1 ◇ S2 ≡ S2 ◇ S1.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma union_preserves_bind `{X : Type} (S1 S2 : set X) k :
  (S1 ◇ S2) >>= k ≡ (S1 >>= k) ◇ (S2 >>= k).
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma empty_cancels_bind `{X : Type} (k : X -> set X) : ∅ >>= k ≡ ∅.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma cong_bind `{X : Type} (S S' : set X) (k k' : X -> set X) :
  S ≡ S' ->
  (forall x, k x ≡ k' x) ->
  S >>= k ≡ S' >>= k'.
Proof.
  intros Heq1 Heq2 ?. split; intros ?; solve_eq_set_base;
    repeat eexists; (apply Heq1 || apply Heq2); eassumption.
Qed.

Create HintDb sets.

Hint Resolve eq_set_refl eq_set_trans eq_set_symm bind_ret_r bind_ret_l
  bind_assoc union_comm union_preserves_bind empty_cancels_bind : sets.

Ltac solve_eq_set := repeat (progress simp_eq_set_goal; eauto with sets).
