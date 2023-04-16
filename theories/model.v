From Coq Require Import String List.
From Metamatix Require Import base.
Import ListNotations.

Record Fact := FACT {
  hypotheses : list Sentence;
  conclusion : Sentence;
}.

(* A corpus is our representation for a metamath database *)
Definition Corpus := list Fact.

Inductive Deduce (Ω : Corpus) : list Sentence -> Sentence -> Prop :=
  | rule_axiom Γ τ :
    τ ∈ Γ -> Deduce Ω Γ τ
  | rule_instance Γ' τ' σ Γ τ :
    (FACT Γ' τ') ∈ Ω ->
    τ'⟨σ⟩ = τ ->
    (forall h, h ∈ Γ' -> Deduce Ω Γ (h⟨σ⟩)) ->
    Deduce Ω Γ τ.

#[local] Notation "U , G ⊢ t" := (Deduce U G t) (at level 80).

Section DeductionExample.

  (* ------------------- *)
  (* forall x : Var, a x *)
  Definition Ω := [FACT [] [Cst "a"; Var "x"]].

  (* τ := a b *)
  Definition τ := [Cst "a"; Cst "b"].

  Goal Ω, [] ⊢ τ.
  Proof.
    eapply (rule_instance _ _ _ (fun _ => [Cst "b"])).
    + now constructor.
    + reflexivity.
    + now intros.
  Qed.

End DeductionExample.
