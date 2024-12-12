Require Import util.

Definition set (X : Type) := X -> Prop.

Definition eq_set `{X : Type} (s1 : set X) (s2 : set X) : Prop :=
  forall x, s1 x <-> s2 x.

Notation "s1 ≡ s2" := (eq_set s1 s2) (at level 80).

Definition empty `{X : Type} : set X :=
  fun _ => False.

Definition member `{X : Type} (x : X) (s : set X) := s x.

Notation "x ∈ s" := (member x s) (at level 80).

Notation "∅" := empty.

Definition union `{X : Type} (s1 : set X) (s2 : set X) : set X :=
  fun x => s1 x \/ s2 x.

Notation "s1 ◇ s2" := (union s1 s2) (at level 70).

Definition ret `{X : Type} (x : X) : set X :=
  fun x' => x = x'.

Definition bind `{X : Type} (s : set X) (f : X -> set X) : set X :=
  fun x => exists x', x' ∈ s /\ x ∈ f x'.

Notation "s >>= f" := (bind s f) (at level 70).

Ltac simp_eq_set_goal := unfold ret, "∅", "∈", "◇", bind, "≡" in *; simpgoal.

Ltac solve_eq_set_base:= repeat (progress simp_eq_set_goal).

Lemma eq_set_refl `{X : Type} (s : set X) : s ≡ s.
Proof.
  intros ?. split; intros ?; solve_eq_set_base.
Qed.

Lemma eq_set_trans `{X : Type} (s1 s2 s3 : set X) :
  s1 ≡ s2 ->
  s2 ≡ s3 ->
  s1 ≡ s3.
Proof.
  intros Heq1 Heq2 ?. split; intros ?; solve_eq_set_base.
  all: specialize (Heq1 x); specialize (Heq2 x); simpgoal.
Qed.

Lemma eq_set_symm `{X : Type} (s1 s2 : set X) :
  s1 ≡ s2 ->
  s2 ≡ s1.
Proof.
  intros Heq ?. split; intros ?; solve_eq_set_base.
  all: specialize (Heq x); solve_eq_set_base.
Qed.

Lemma bind_ret_r `{X : Type} (s : set X) : (s >>= ret) ≡ s.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma bind_ret_l `{X : Type} (x : X) f : (ret x >>= f) ≡ f x.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.
    
Lemma bind_assoc `{X : Type} (s : set X) f g :
  (s >>= f) >>= g ≡ s >>= (fun x => f x >>= g).
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma union_comm `{X : Type} (s1 s2 : set X) : s1 ◇ s2 ≡ s2 ◇ s1.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma union_preserves_bind `{X : Type} (s1 s2 : set X) k :
  (s1 ◇ s2) >>= k ≡ (s1 >>= k) ◇ (s2 >>= k).
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma empty_cancels_bind `{X : Type} (k : X -> set X) : ∅ >>= k ≡ ∅.
Proof. intros ?. split; intros ?; solve_eq_set_base. Qed.

Lemma cong_bind `{X : Type} (s s' : set X) (k k' : X -> set X) :
  s ≡ s' ->
  (forall x, k x ≡ k' x) ->
  s >>= k ≡ s' >>= k'.
Proof.
  intros Heq1 Heq2 ?. split; intros ?; solve_eq_set_base;
    repeat eexists; (apply Heq1 || apply Heq2); eassumption.
Qed.

Create HintDb sets.

Hint Resolve eq_set_refl eq_set_trans eq_set_symm bind_ret_r bind_ret_l
  bind_assoc union_comm union_preserves_bind empty_cancels_bind : sets.

Ltac solve_eq_set := repeat (progress simp_eq_set_goal; eauto with sets).

