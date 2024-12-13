From Coq Require Export Arith.PeanoNat.
Require Export Lia.
From Coq Require Export Logic.FunctionalExtensionality.

Ltac simp :=
  match goal with
  | [ p : (_ * _)%type |- _ ] => destruct p
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ <-> _ |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  | [ |- _ /\ _ ] => split
  | [ H : (_,_) = (_,_) |- _ ] =>
      injection H ; clear H ; intros ; try subst
  | [ H : Some _ = Some _ |- _ ] =>
      injection H ; clear H ; intros ; try subst
  | [ H : Some _ = None |- _ ] => congruence
  | [ H : None = Some _ |- _ ] => congruence
  | [ H : ?x <> ?x |- _ ] => congruence
  | [ H : ~ True |- _ ] => contradiction H ; auto
  | [ H : False |- _ ] => contradiction H ; auto
  | [ |- forall _, _ ] => intros
  | [ H : ?x = ?y |- _ ] => subst
  | [ H : _ \/ _ |- _ ] => destruct H
  | _ => eauto
  end.

Ltac simpgoal := repeat (simpl in *; simp).
