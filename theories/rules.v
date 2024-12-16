Require Import assertion ol syntax.

Reserved Notation "⊢atom ⟨ P ⟩ c ⟨ Q ⟩".

Inductive rules_atom : prop -> cmd -> prop -> Prop :=
| RuleAssign x e :
  ⊢atom ⟨ ok ⟩ x <- e ⟨ x == e ⟩
| RuleAlloc x :
  ⊢atom ⟨ ok ⟩ x <- alloc ⟨ var x --> - ⟩
| RuleStoreOk e1 e2 :
  ⊢atom ⟨ e1 --> - ⟩ [ e1 ] <- e2 ⟨ e1 --> e2 ⟩
| RuleStoreErr e1 e2 :
  ⊢atom ⟨ e1 -/-> ⟩ [ e1 ] <- e2 ⟨ error ⟩
| RuleLoadOk e e' x :
  ⊢atom ⟨ e --> e' ⟩ x <- [ e ] ⟨ x == e' ⟩
| RuleLoadErr x e :
  ⊢atom ⟨ e -/-> ⟩ x <- [ e ] ⟨ error ⟩
where "⊢atom ⟨ P ⟩ c ⟨ Q ⟩" := (rules_atom P c Q).

Reserved Notation "⊢ ⟨ phi ⟩ C ⟨ psi ⟩".

Inductive rules : assertion -> cl -> assertion -> Prop :=
| RuleZero phi : ⊢ ⟨ phi ⟩ 𝟘 ⟨ ⊤⊕ ⟩
| RuleOne phi : ⊢ ⟨ phi ⟩ 𝟙 ⟨ phi ⟩
| RuleSeq phi psi theta C1 C2 :
  ⊢ ⟨ phi ⟩ C1 ⟨ psi ⟩ ->
  ⊢ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
  ⊢ ⟨ phi ⟩ C1 ⨟ C2 ⟨ theta ⟩
| RuleSplit phi1 psi1 phi2 psi2 C :
  ⊢ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
  ⊢ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
  ⊢ ⟨ phi1 ⊕ phi2 ⟩ C ⟨ psi1 ⊕ psi2 ⟩
| RuleConsequence phi phi' psi psi' C :
  (forall S, S ⊨ phi' ⇒ phi) ->
  ⊢ ⟨ phi ⟩ C ⟨ psi ⟩ ->
  (forall S, S ⊨ psi ⇒ psi') ->
  ⊢ ⟨ phi' ⟩ C ⟨ psi' ⟩
| RuleEmpty C : ⊢ ⟨ ⊤⊕ ⟩ C ⟨ ⊤⊕ ⟩
| RuleTrue phi C : ⊢ ⟨ phi ⟩ C ⟨ ⊤ ⟩
| RuleFalse C phi : ⊢ ⟨ ⊥ ⟩ C ⟨ phi ⟩
| RulePlus phi psi1 psi2 C1 C2 :
  ⊢ ⟨ phi ⟩ C1 ⟨ psi1 ⟩ ->
  ⊢ ⟨ phi ⟩ C2 ⟨ psi2 ⟩ ->
  ⊢ ⟨ phi ⟩ C1 + C2 ⟨ psi1 ⊕ psi2 ⟩
| RuleInduction phi psi C :
  ⊢ ⟨ phi ⟩ 𝟙 + C ⨟ C ⋆ ⟨ psi ⟩ ->
  ⊢ ⟨ phi ⟩ C ⋆ ⟨ psi ⟩
| RuleCmd P Q c :
  ⊢atom ⟨ P ⟩ c ⟨ Q ⟩ ->
  ⊢ ⟨ P ⟩ c ⟨ Q ⟩
where "⊢ ⟨ phi ⟩ C ⟨ psi ⟩" := (rules phi C psi).
