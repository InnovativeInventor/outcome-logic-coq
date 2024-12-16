Require Import syntax.
Require Import util.
Require Import vec.

(* Values that can be stored in the heap + stack: naturals or null *)
Definition value := option nat.

Definition is_true (v : value) : Prop :=
  match v with
  | Some n => n > 0
  | None => False
  end.

Definition is_false (v : value) : Prop :=
  match v with
  | Some n => n = 0
  | None => True
  end.

(* The local stack + associated operations/lemmas *)
Definition stack := nat -> value.

Definition empty_stack : stack := fun _ => None.

Definition insert (x : nat) (v : value) (s : stack) : stack :=
  fun y => if Nat.eq_dec x y then v else s y.

Lemma lookup_insert x v s : (insert x v s) x = v.
Proof.
  intros. unfold insert. destruct (Nat.eq_dec x x); congruence.
Qed.

(* The heap + associated operations/lemmas *)
Definition heap := { n & vec n value }.

Definition empty_heap : heap := existT _ O  tt.

Definition newptr (h : heap) : heap * nat :=
  match h with
  | existT _ n l => (existT _ (S n) (append l None) , n)
  end.

Definition load (h : heap) (i : nat) : option value :=
  match h with
  | existT _ _ l => find l i
  end.

Definition hasptr (h : heap) (i : nat) : Prop :=
  match h with
  | existT _ n _ => i < n
  end.

Definition store (h : heap) (i : nat) (v : value) : heap :=
  match h with
  | existT _ n l =>
      existT _ n (update l i v)
  end.

Definition mapsto (h : heap) (i : nat) (v : value) : Prop :=
  match load h i with
  | None => False
  | Some v' => v = v'
  end.

(* A program state is either a stack and a heap or a memory error *)
Definition state := ((stack * heap) + unit)%type.

Definition good_state (s : stack) (h : heap) : state := inl (s , h).

Notation "<{ s , h }>" := (good_state s h).

Definition empty_state : state := <{ empty_stack, empty_heap }>.

Definition mem_err : state := inr tt.

Notation "'err'" := mem_err.
