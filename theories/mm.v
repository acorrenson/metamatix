From Coq Require Import String List Arith Bool.
Import ListNotations.

Section Model.

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

Definition Ω := [PROP [] [Cst "a"; Var 0]].
Definition τ := [Cst "a"; Cst "b"].

Goal Ω, [] ⊢ τ.
Proof.
  eapply (rule_instance _ _ _ (fun _ => [Cst "b"])).
  + now constructor.
  + reflexivity.
  + now intros.
Qed.

End Model.


Section Mm.

Inductive Label :=
  | TypeLbl (lbl : nat)
  | FactLbl (lbl : nat)
  | RuleLbl (lbl : nat).

Inductive Statement :=
  | Ax (stmt : Term)
  | Th (stmt : Term) (proof : list Label).

Record Rule := RULE {
  type_hypothesis : list (nat * (string * nat));
  fact_hypothesis : list (nat * Term);
  statement    : Statement;
}.

Record File := FILE {
  (* variables : list nat;
  constants : list string; *)
  rules     : list (nat * Rule);
}.

Fixpoint get {A} (l : list (nat * A)) (x : nat) : option A :=
  match l with
  | [] => None
  | (y, vy)::xs =>
    if (x =? y)%nat then
      Some vy
    else
      get xs x
  end.

Definition Stack := list Term.
Definition Binding : Type := (nat * Term).
Definition Unifier := list Binding.

Fixpoint binds (u : Unifier) (x : nat) :=
  match u with
  | [] => false
  | (v, _)::u =>
    (x =? v)%nat || binds u x
  end.

Fixpoint unify (Σ : Stack) (unifier : Unifier) (type_hyps : list (nat * (string * nat))) : option (Stack * Unifier) :=
  match Σ, type_hyps with
  | [], [] => Some ([], [])
  | [], _  => None
  | (Cst ty::τ)::Σ, (_, (ty', v))::type_hyps =>
    if binds unifier v then None
    else if (ty =? ty')%string then
      unify Σ ((v, τ)::unifier) type_hyps
    else None
  | _, _ => None
  end.

Definition as_subst (unifier : Unifier) : (nat -> Term) :=
  fun x =>
    match get unifier x with
    | None => [Var x]
    | Some τ => τ
    end.

Notation "τ '.⟨' σ '⟩'" := (substitute τ (as_subst σ)) (at level 80).

Fixpoint apply_unifier (unifier : Unifier) (Σ : Stack) : Stack :=
  match Σ with
  | [] => []
  | τ::Σ =>
    (substitute τ (as_subst unifier))::apply_unifier unifier Σ
  end.

Fixpoint term_eqb (τ1 τ2 : Term) : bool :=
  match τ1, τ2 with
  | [], [] => true
  | (Cst x)::xs, (Cst y)::ys =>
    (x =? y)%string && term_eqb xs ys
  | (Var x)::xs, (Var y)::ys =>
    (x =? y)%nat && term_eqb xs ys
  | _, _ => false
  end.

Declare Scope term.
Delimit Scope term with term.
Notation "x =? y" := (term_eqb x y)%term.

Fixpoint match_facts (Σ : Stack) (fact_hyps : list (nat * Term)) : option Stack :=
  match Σ, fact_hyps with
  | [], [] => Some []
  | τ::Σ, (_, τ')::fact_hyps =>
    if (τ =? τ')%term then
      match_facts Σ fact_hyps
    else
      None
  | _, _ => None
  end.

Inductive status :=
  | UnificationFailed
  | MatchingFailed
  | StackUnderflow
  | StackOverflow
  | UndefinedType (id : nat)
  | UndefinedFact (id : nat)
  | UndefinedRule (id : nat)
  | WrongStmt (τ : Term)
  | Assumed (τ : Term)
  | Proved (τ : Term).

Definition term (s : Statement) : Term :=
  match s with
  | Ax τ => τ
  | Th τ _ => τ
  end.

Fixpoint exec_proof (F : File) (Σ : Stack) type_hyps fact_hyps proof :=
  match proof with
  | [] =>
    match Σ with
    | [] => StackUnderflow
    | [τ] => Proved τ
    | _ => StackOverflow
    end
  | TypeLbl lbl::proof =>
    match get type_hyps lbl with
    | Some (ty, v) => exec_proof F ([Cst ty; Var v]::Σ) type_hyps fact_hyps proof
    | None => UndefinedType lbl
    end
  | FactLbl lbl::proof =>
    match get fact_hyps lbl with
    | Some f => exec_proof F (f::Σ) type_hyps fact_hyps proof
    | None => UndefinedFact lbl
    end
  | RuleLbl lbl::proof =>
    match get (rules F) lbl with
    | Some (RULE r_type_hyps r_fact_hyps r_stmt) =>
      match unify Σ [] r_type_hyps with
      | Some (Σ, unifier) =>
        match match_facts (apply_unifier unifier Σ) r_fact_hyps with
        | Some Σ => exec_proof F ((term r_stmt).⟨unifier⟩::Σ) type_hyps fact_hyps proof
        | None => MatchingFailed
        end
      | None => UnificationFailed
      end
    | None => UndefinedRule lbl
    end
  end.

Definition check (F : File) (R : Rule) : status :=
  match statement R with
  | Ax stmt => Assumed stmt
  | Th stmt proof =>
    match exec_proof F [] (type_hypothesis R) (fact_hypothesis R) proof with
    | Proved stmt' =>
      if (stmt =? stmt')%term then Proved stmt
      else WrongStmt stmt'
    | status => status
    end
  end.

Example my_rule := RULE [(0, ("wff"%string, 0))] [] (Ax [Cst "a"; Var 0]).
Example my_file := FILE [(0, my_rule)].
Example my_thm := RULE [(0, ("wff"%string, 0))] [] (Th [Cst "a"; Var 0] [TypeLbl 0; RuleLbl 0]).
Compute (check my_file my_thm).

End Mm.


Section Soundness.
(* Definition interp_Rule (R : Rule) : Proposition := *)
End Soundness.
