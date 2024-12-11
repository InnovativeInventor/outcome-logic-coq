From Coq Require Import Arith.PeanoNat.

Require Export syntax.

Definition value := nat.

Definition state := nat -> value.

Definition insert (x : nat) (v : value) (σ : state) : state :=
  fun y => if Nat.eq_dec x y then v else σ y.

Definition expr_to_value (e : expr) (σ : state) : value :=
  match e with
  | Var x => σ x
  | Lit n => n
  end.

Inductive eval_cmd : cmd -> state -> state -> Prop :=
| EvalAssume e σ :
  expr_to_value e σ > 0 ->
  eval_cmd (assume e) σ σ
| EvalAssign x e σ σ' :
  σ' = insert x (expr_to_value e σ) σ ->
  eval_cmd (x <- e) σ σ'
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
