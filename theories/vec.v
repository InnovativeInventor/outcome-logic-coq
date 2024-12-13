Require Import Lia.
Require Import util.

Fixpoint vec (n : nat) (A : Type) : Type :=
  match n with
  | O => unit
  | S n => (A * vec n A)%type
  end.

Definition append `{A : Type} `{n : nat} (l : vec n A) (a : A) : vec (S n) A :=
  (a , l).

Fixpoint lookup `{A : Type} `{n : nat} (l : vec n A) (i : nat) : option A :=
  match n return (vec n A -> option A) with
  | O => fun _ => None
  | S n => fun '(a , l) =>
             match i with
             | O => Some a
             | S i => lookup l i
             end
  end l.

Fixpoint update `{A : Type} `{n : nat} (l : vec n A) (i : nat) (a : A) : vec n A :=
  match n return (vec n A -> vec n A) with
  | O => fun l => l
  | S n => fun '(a' , l') =>
             match i with
             | O => (a , l')
             | S i => (a' , update l' i a)
             end
  end l.
    
Theorem lookup_le `{A : Type} `{n : nat} (l : vec n A) (i : nat) :
  i < n ->
  exists a, lookup l i = Some a.
Proof.
  revert i l. induction n.
  - intros ?? Hc. inversion Hc.
  - intros ??. induction i; intros; simpgoal.
    assert (i < n) by lia. simpgoal.
Qed.

Theorem update_le `{A : Type} `{n : nat} (l : vec n A) (i : nat) (a : A) :
  i < n ->
  lookup (update l i a) i = Some a.
Proof.
  revert i l a. induction n.
  - intros ??? Hc. inversion Hc.
  - intros ???. induction i; intros; simpgoal.
    assert (i < n) by lia. simpgoal.
Qed.
