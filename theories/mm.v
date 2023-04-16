From Coq Require Import String List Arith Bool.
From Metamatix Require Import model.
Import ListNotations.

Section Mm.

Inductive Label :=
  | TypeLbl (lbl : string)
  | FactLbl (lbl : string)
  | RuleLbl (lbl : string).

Inductive Statement :=
  | Ax (stmt : Sentence)
  | Th (stmt : Sentence) (proof : list Label).

Record Rule := RULE {
  type_hypotheses : list (string * (string * string));
  fact_hypotheses : list (string * Sentence);
  statement    : Statement;
}.

Record File := FILE {
  (* variables : list nat;
  constants : list string; *)
  rules     : list (string * Rule);
}.

Fixpoint get {A} (l : list (string * A)) (x : string) : option A :=
  match l with
  | [] => None
  | (y, vy)::xs =>
    if (x =? y)%string then
      Some vy
    else
      get xs x
  end.

Definition Stack := list Sentence.
Definition Binding : Type := (string * Sentence).
Definition Unifier := list Binding.

Fixpoint binds (u : Unifier) (x : string) :=
  match u with
  | [] => false
  | (v, _)::u =>
    (x =? v)%string || binds u x
  end.

Definition mbind [A B] (m : option A) (f : A -> option B) : option B :=
  match m with
  | Some a => f a
  | None   => None
  end.

Definition mret  [A] (a : A)    : option A := Some a.
Definition mfail [A] (u : unit) : option A := None.
Definition when   (b : bool)   := if b then Some tt else None.
Definition unless (b : bool)   := when (negb b).

Notation "a <- x ;; y" := (mbind x (fun a => y)) (at level 80).
Notation "x ;; y" := (mbind x (fun _ => y)) (at level 80).

Fixpoint unify (Σ : Stack) (unifier : Unifier)
               (type_hyps : list (string * (string * string)))
             : option (Stack * Unifier) :=
  match Σ, type_hyps with
  | [], [] => mret ([], unifier)
  | (Cst ty::τ)::Σ, (_, (ty', v))::type_hyps =>
    unless (binds unifier v) ;;
    when (ty =? ty')%string  ;;
    unify Σ ((v, τ)::unifier) type_hyps
  | _, _ => mfail tt
  end.

Definition as_subst (unifier : Unifier) : (string -> Sentence) :=
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

Fixpoint term_eqb (τ1 τ2 : Sentence) : bool :=
  match τ1, τ2 with
  | [], [] => true
  | (Cst x)::xs, (Cst y)::ys =>
    (x =? y)%string && term_eqb xs ys
  | (Var x)::xs, (Var y)::ys =>
    (x =? y)%string && term_eqb xs ys
  | _, _ => false
  end.

Declare Scope term.
Delimit Scope term with term.
Notation "x =? y" := (term_eqb x y)%term.

Fixpoint match_facts (Σ : Stack) (fact_hyps : list (string * Sentence)) : option Stack :=
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
  | UndefinedType (id : string)
  | UndefinedFact (id : string)
  | UndefinedRule (id : string)
  | WrongStmt (τ : Sentence)
  | Assumed (τ : Sentence)
  | Proved (τ : Sentence).

Definition term (s : Statement) : Sentence :=
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
    match exec_proof F [] (type_hypotheses R) (fact_hypotheses R) proof with
    | Proved stmt' =>
      if (stmt =? stmt')%term then Proved stmt
      else WrongStmt stmt'
    | status => status
    end
  end.

Example my_rule := RULE [("wffx", ("wff", "x"))]%string [] (Ax [Cst "a"; Var "x"]).
Example my_file := FILE [("rule_1", my_rule)]%string.
Example my_thm := RULE [("wffy", ("wff", "y"))]%string [] (Th [Cst "a"; Var "y"] [TypeLbl "wffy"; RuleLbl "rule_1"]).
Compute (check my_file my_thm).
Compute (unify [[Cst "wff"; Var "x"]] [] [("hyp1", ("wff", "y"))])%string.

End Mm.
