From Coq Require Import String List.
Import ListNotations.

Inductive Symbol :=
  | Var (v : string)
  | Cst (c : string).

Definition Sentence := list Symbol.

Record Fact := PROP {
  hypotheses : list Sentence;
  conclusion : Sentence;
}.

(* A corpus is our representation for a metamath database *)
Definition Corpus := list Fact.

(* Substitute all variables by their projection under σ *)
Fixpoint substitute (τ : Sentence) (σ : string -> Sentence) : Sentence :=
  match τ with
  | [] => []
  | Var v::τ => (σ v) ++ (substitute τ σ)
  | x::τ => x::(substitute τ σ)
  end.

Notation "x ∈ L" := (In x L) (at level 80).
Notation "τ '⟨' σ '⟩'" := (substitute τ σ) (at level 80).

Inductive Deduce (Ω : Corpus) : list Sentence -> Sentence -> Prop :=
  | rule_axiom Γ τ :
    τ ∈ Γ -> Deduce Ω Γ τ
  | rule_instance Γ' τ' σ Γ τ :
    (PROP Γ' τ') ∈ Ω ->
    τ'⟨σ⟩ = τ ->
    (forall h, h ∈ Γ' -> Deduce Ω Γ (h⟨σ⟩)) ->
    Deduce Ω Γ τ.

#[local] Notation "U , G ⊢ t" := (Deduce U G t) (at level 80).

Section DeductionExample.

  (* ------------------- *)
  (* forall x : Var, a x *)
  Definition Ω := [PROP [] [Cst "a"; Var "x"]].

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
