Require Export state.
Require Export syntax.

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

Inductive eval_cmd : cmd -> state -> state -> Prop :=
| EvalAssume e s h v :
  eval_expr e s = v ->
  is_true v ->
  eval_cmd e <{s, h}> <{s, h}>
| EvalNot e s h v :
  eval_expr e s = v ->
  is_false v ->
  eval_cmd (¬ e) <{s, h}> <{s, h}>
| EvalAssign x e s s' h :
  s' = insert x (eval_expr e s) s ->
  eval_cmd (x <- e) <{s, h}> <{s', h}>
| EvalAlloc x s s' h h' i :
  (h' , i) = newptr h ->
  s' = insert x (Some i) s ->
  eval_cmd (x <- alloc) <{s, h}> <{s', h'}>
| EvalLoad x e s s' h i v :
  isnat s e i ->
  mapsto h i v ->
  s' = insert x v s ->
  eval_cmd (x <- [ e ]) <{s, h}> <{s', h}>
| EvalLoadNull x e s h :
  eval_expr e s = None ->
  eval_cmd (x <- [ e ]) <{s, h}> err
| EvalStore e1 e2 s h h' i v :
  isnat s e1 i ->
  eval_expr e2 s = v ->
  hasptr h i ->
  h' = store h i v ->
  eval_cmd ([ e1 ] <- e2) <{s, h}> <{s, h'}>
| EvalStoreNull e1 e2 s h :
  eval_expr e1 s = None ->
  eval_cmd ([ e1 ] <- e2) <{s, h}> err
.

Hint Resolve EvalAssume EvalNot EvalAssign EvalAlloc EvalLoad
  EvalLoadNull EvalStore EvalStoreNull : core.

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
