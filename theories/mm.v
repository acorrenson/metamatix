From Coq Require Import String List.
Import ListNotations.

Module Model.

Inductive Symbol :=
  | Var (v : nat)
  | Cst (c : string).

Definition Term := list Symbol.

Definition Context := list Term.

Record Proposition := PROP {
  hypothesis : Context;
  conclusion : Term;
}.

Definition Universe := list Proposition.

Fixpoint substitute (τ : Term) (σ : nat -> Term) : Term :=
  match τ with
  | [] => []
  | Var v::τ => (σ v) ++ (substitute τ σ)
  | x::τ => x::(substitute τ σ)
  end.

Notation "x ∈ L" := (In x L) (at level 80).
Notation "τ '⟨' σ '⟩'" := (substitute τ σ) (at level 80).

Inductive Deduce (Ω : Universe) : Context -> Term -> Prop :=
  | rule_axiom Γ τ :
    τ ∈ Γ -> Deduce Ω Γ τ
  | rule_instance Γ' τ' σ Γ τ :
    (PROP Γ' τ') ∈ Ω ->
    τ'⟨σ⟩ = τ ->
    (forall h, h ∈ Γ' -> Deduce Ω Γ (h⟨σ⟩)) ->
    Deduce Ω Γ τ.

Notation "U , G ⊢ t" := (Deduce U G t) (at level 80).

End Model.

