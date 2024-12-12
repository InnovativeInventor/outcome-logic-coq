From Coq Require Import Arith.PeanoNat.

Require Export syntax.
Require Import vec.

Definition value := option nat.

Definition stack := nat -> value.
Definition heap := { n & vec n nat }.

Definition newptr (h : heap) : heap * nat :=
  match h with
  | existT _ n l => (existT _ (S n) (append l 0) , n)
  end.

Definition read (h : heap) (n : nat) : value :=
  match h with
  | existT _ n l => lookup l n
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

Inductive eval_cmd : cmd -> state -> state -> Prop :=
| EvalAssume e s h n :
  eval_expr e s = Some n ->
  n > 0 ->
  eval_cmd e <{s, h}> <{s, h}>
| EvalNot e s h n :
  eval_expr e s = Some n ->
  n = 0 ->
  eval_cmd e <{s, h}> <{s, h}>
| EvalAssign x e s s' h :
  s' = insert x (eval_expr e s) s ->
  eval_cmd (x <- e) <{s, h}> <{s', h}>
| EvalAlloc x s s' h h' n :
  (h' , n) = newptr h ->
  s' = insert x (Some n) s ->
  eval_cmd (x <- alloc) <{s, h}> <{s', h'}>
| EvalRead x e s s' h n n' :
  eval_expr e s = Some n ->
  read h n = Some n' ->
  s' = insert x (Some n') s ->
  eval_cmd (x <- [ e ]) <{s, h}> <{s', h}>
| EvalReadNull x e s h :
  eval_expr e s = None ->
  eval_cmd (x <- [ e ]) <{s, h}> err
| EvalReadInvalidPtr x e s h n :
  (* todo: change heap to nat -> nat OR change heap to finite map *)
  eval_expr e s = Some n ->
  read h n = None ->
  eval_cmd (x <- [ e ]) <{s, h}> err
(* TODO: eval write, eval write error *)
.

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
