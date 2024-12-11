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

Lemma bind_ret_r `{X : Type} (s : set X) : (s >>= ret) ≡ s.
Proof.
  intros x. split; intros H.
  - destruct H as [? [? ?]]. unfold ret, "∈" in *. subst. assumption.
  - eexists. split; eauto. reflexivity.
Qed.

Lemma bind_ret_l `{X : Type} (x : X) f : (ret x >>= f) ≡ f x.
Proof.
  intros ?. split; intros H.
  - destruct H as [? [? ?]]. unfold ret, "∈" in *. subst. assumption.
  - eexists. split; eauto. reflexivity.
Qed.
    
Lemma bind_assoc `{X : Type} (s : set X) f g :
  (s >>= f) >>= g ≡ s >>= (fun x => f x >>= g).
Proof.
  intros ?. split; intros H.
  - repeat destruct H as [? [? ?]].
    repeat (eexists; split; eauto).
  - repeat destruct H as [? [? H]].
    repeat (eexists; split; eauto).
Qed.

Lemma union_comm `{X : Type} (s1 s2 : set X) : s1 ◇ s2 ≡ s2 ◇ s1.
Proof.
  intros ?. split; intros.
  - destruct H.
    + right. assumption.
    + left. assumption.
  - destruct H.
    + right. assumption.
    + left. assumption.
Qed.

Lemma union_preserves_bind `{X : Type} (s1 s2 : set X) k :
  (s1 ◇ s2) >>= k ≡ (s1 >>= k) ◇ (s2 >>= k).
Proof.
  intros ?. split; intros H.
  - destruct H as [? [? ?]]. destruct H.
    + left. eexists. split; eassumption.
    + right. eexists. split; eassumption.
  - destruct H; destruct H as [? [? ?]].
    + eexists. split. left. all: eassumption.
    + eexists. split. right. all: eassumption.
Qed.

Lemma empty_cancels_bind `{X : Type} (k : X -> set X) : ∅ >>= k ≡ ∅.
Proof.
  intros ?. split; intros H.
  1: destruct H as [? [? ?]].
  all: inversion H.
Qed.
