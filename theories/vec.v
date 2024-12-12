Require Import Lia.
Require Import util.

Fixpoint vec (n : nat) (A : Type) : Type :=
  match n with
  | O => unit
  | S n => (A * vec n A)%type
  end.

Definition append `{A : Type} `{n : nat} (l : vec n A) (a : A) : vec (S n) A :=
  (a , l).

Fixpoint lookup `{A : Type} `{n : nat} (l : vec n A) (m : nat) : option A :=
  match n return (vec n A -> option A) with
  | O => fun _ => None
  | S n => fun '(a , l) =>
             match m with
             | O => Some a
             | S m => lookup l m
             end
  end l.

Theorem lookup_le `{A : Type} `{n : nat} (l : vec n A) (m : nat) :
  m < n ->
  exists a, lookup l m = Some a.
Proof.
  revert m l. induction n.
  - intros ?? Hc. inversion Hc.
  - intros ??. induction m; intros Hle.
    + destruct l; simpgoal.
    + destruct l as [a' l]. assert (m < n) by lia; simpgoal.
Qed.
