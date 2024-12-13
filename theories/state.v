Require Import syntax.
Require Import util.
Require Import vec.

Definition value := option nat.

Definition stack := nat -> value.
Definition heap := { n & vec n value }.

Definition empty_stack : stack := fun _ => None.
Definition empty_heap : heap := existT _ O  tt.

Definition newptr (h : heap) : heap * nat :=
  match h with
  | existT _ n l => (existT _ (S n) (append l None) , n)
  end.

Definition read (h : heap) (i : nat) : option value :=
  match h with
  | existT _ _ l => lookup l i
  end.

Definition hasptr (h : heap) (i : nat) : Prop :=
  match h with
  | existT _ n _ => i < n
  end.

Definition write (h : heap) (i : nat) (v : value) : heap :=
  match h with
  | existT _ n l =>
      existT _ n (update l i v)
  end.

Definition state := ((stack * heap) + unit)%type.

Definition good_state (s : stack) (h : heap) : state := inl (s , h).

Notation "<{ s , h }>" := (good_state s h).

Definition empty_state : state := <{ empty_stack, empty_heap }>.

Definition mem_err : state := inr tt.

Notation "'err'" := mem_err.

Definition insert (x : nat) (v : value) (s : stack) : stack :=
  fun y => if Nat.eq_dec x y then v else s y.

Definition eval_expr (e : expr) (s : stack) : value :=
  match e with
  | Var x => s x
  | Lit n => Some n
  | Null => None
  end.

Definition isnat (s : stack) (e : expr) (n : nat) : Prop :=
  match eval_expr e s with
  | None => False
  | Some n' => n = n'
  end.

Definition mapsto (h : heap) (i : nat) (v : value) : Prop :=
  match read h i with
  | None => False
  | Some v' => v = v'
  end.

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

Lemma value_eq_dec (v1 v2 : value) : {v1 = v2} + {v1 <> v2}.
Proof.
  destruct v1 as [n1|]; destruct v2 as[n2|].
  - destruct (Nat.eq_dec n1 n2).
    + left. congruence.
    + right. congruence.
  - right. congruence.
  - right. congruence.
  - left. reflexivity.
Qed.

Lemma lookup_insert x v s : (insert x v s) x = v.
Proof. 
  intros. unfold insert. destruct (Nat.eq_dec x x); congruence.
Qed.

                       
