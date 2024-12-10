Unset Universe Checking.

Require Import computation.
Require Export syntax.

Definition insert (x : nat) (v : value) (σ : state) : state :=
  fun y => if Nat.eq_dec x y then v else σ y.

Definition denote_expr (e : expr) (σ : state) : value :=
  match e with
  | Var x => σ x
  | Lit n => n
  end.

Definition value_to_bool (v : value) : bool :=
  match v with
  | 0 => false
  | _ => true
  end.

Definition denote_cmd (c : cmd) (σ : state) : computation state :=
  match c with
  | assume e =>
      if value_to_bool (denote_expr e σ) then ret σ else ∅
  | assign x e =>
      ret (insert x (denote_expr e σ) σ)
  end.

Reserved Notation "⟦ C ⟧".

Fixpoint denote (C : cl) (σ : state) : computation state :=
  match C with
  | 𝟘 => ∅
  | 𝟙 => ret σ
  | C1 ⨟ C2 => ⟦ C1 ⟧ σ >>= ⟦ C2 ⟧
  | C1 + C2 => ⟦ C1 ⟧ σ ◇ ⟦ C2 ⟧ σ
  | C ⋆ =>
      iter (fun σ' =>
              (σ'' <-  ⟦ C ⟧ σ' ;; ret (inl σ''))
                ◇
              ret (inr σ')) σ
  | Atom cmd => denote_cmd cmd σ
  end
where "⟦ C ⟧" := (denote C).
