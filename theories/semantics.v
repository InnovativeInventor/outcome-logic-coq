From Coq Require Import Arith.PeanoNat.

Require Export syntax.
Require Import vec.

Definition value := option nat.

Definition stack := nat -> value.
Definition heap := { n & vec n value }.

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

Inductive eval_cmd : cmd -> state -> state -> Prop :=
| EvalAssume e s h v :
  eval_expr e s = v ->
  is_true v ->
  eval_cmd e <{s, h}> <{s, h}>
| EvalNot e s h v :
  eval_expr e s = v ->
  is_false v ->
  eval_cmd e <{s, h}> <{s, h}>
| EvalAssign x e s s' h :
  s' = insert x (eval_expr e s) s ->
  eval_cmd (x <- e) <{s, h}> <{s', h}>
| EvalAlloc x s s' h h' i :
  (h' , i) = newptr h ->
  s' = insert x (Some i) s ->
  eval_cmd (x <- alloc) <{s, h}> <{s', h'}>
| EvalRead x e s s' h i v :
  isnat s e i ->
  mapsto h i v ->
  s' = insert x v s ->
  eval_cmd (x <- [ e ]) <{s, h}> <{s', h}>
| EvalReadNull x e s h :
  eval_expr e s = None ->
  eval_cmd (x <- [ e ]) <{s, h}> err
| EvalWrite e1 e2 s h h' i v :
  isnat s e1 i ->
  eval_expr e2 s = v ->
  hasptr h i ->
  h' = write h i v ->
  eval_cmd ([ e1 ] <- e2) <{s, h}> <{s, h'}>
| EvalWriteNull e1 e2 s h :
  eval_expr e1 s = None ->
  eval_cmd ([ e1 ] <- e2) <{s, h}> err
.

Hint Resolve EvalAssume EvalNot EvalAssign EvalAlloc EvalRead
  EvalReadNull EvalWrite EvalWriteNull : core.

Reserved Notation "x ⇓ y" (at level 80).

Inductive eval : (cl * state) -> state -> Prop :=
| EvalOne σ : (𝟙 , σ) ⇓ σ
| EvalSeq C1 C2 σ σ' σ'' :
  (C1 , σ) ⇓ σ' ->
  (C2 , σ') ⇓ σ'' ->
  (C1 ⨟ C2 , σ) ⇓ σ''
| EvalBr1 C1 C2 σ σ' :
  (C1 , σ) ⇓ σ' ->
  (C1 + C2 , σ) ⇓ σ'
| EvalBr2 C1 C2 σ σ' :
  (C2 , σ) ⇓ σ' ->
  (C1 + C2 , σ) ⇓ σ'
| EvalStar0 C σ :
  (C ⋆ , σ) ⇓ σ
| EvalStar1 C σ σ' :
  (C ⨟ C ⋆ , σ) ⇓ σ' ->
  (C ⋆ , σ) ⇓ σ'
| EvalCmd c σ σ' :
  eval_cmd c σ σ' ->
  (Atom c , σ) ⇓ σ'
where "x ⇓ y" := (eval x y).

Hint Resolve EvalOne EvalSeq EvalBr1 EvalBr2
  EvalStar0 EvalStar1 EvalCmd : core.
