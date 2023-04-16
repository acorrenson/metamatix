From Coq Require Import String List Arith Bool.
From Metamatix Require Import base model.
Import ListNotations.

(* we differentiate between three different kinds of objects in a proof:
   * types (symbols that define what the nature of a variable is)
      e.g. in set.mm there is a type 'wff' of well-formed formulas
   * fact (refers to an assumption in the current context)
   * rule (anything that is an axiom or a theorem that has been proven) *)
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

(* Tests whether `x` has a binding in `u` *)
Fixpoint binds (u : Unifier) (x : string) :=
  match u with
  | [] => false
  | (v, _)::u =>
    (x =? v)%string || binds u x
  end.

Fixpoint unify (Σ : Stack) (unifier : Unifier)
               (type_hyps : list (string * (string * string)))
             : option (Stack * Unifier) :=
  match Σ, type_hyps with
  | [], [] => mret ([], unifier)
  | (Cst ty::τ)::Σ, (_, (ty', v))::type_hyps =>
    unless (binds unifier v) ;; (* ensure v does not yet have a value in the unifier *)
    assert (ty =? ty')%string  ;; (* ensure the expected type of v matches the witness provided by the user *)
    unify Σ ((v, τ)::unifier) type_hyps (* adds a binding that maps `v` to `τ` *)
  | _, _ => mfail tt
  end.

(* interpret a list of pairs as a map *)
Definition as_subst (unifier : Unifier) : (string -> Sentence) :=
  fun x =>
    match get unifier x with
    | None => [Var x]
    | Some τ => τ
    end.

Notation "τ '.⟨' σ '⟩'" := (substitute τ (as_subst σ)) (at level 80).

Fixpoint inst (ls : list (string * Sentence)) (unifier : Unifier) : list (string * Sentence) :=
  match ls with
  | [] => []
  | (lbl,τ)::ls =>
    (lbl, substitute τ (as_subst unifier))::inst ls unifier
  end.

(* TODO: define Subst type class with substitute and inst as instances *)

(* decidable equality of sentence *)
Fixpoint sentence_eqb (τ1 τ2 : Sentence) : bool :=
  match τ1, τ2 with
  | [], [] => true
  | (Cst x)::xs, (Cst y)::ys =>
    (x =? y)%string && sentence_eqb xs ys
  | (Var x)::xs, (Var y)::ys =>
    (x =? y)%string && sentence_eqb xs ys
  | _, _ => false
  end.

Declare Scope mm.
Delimit Scope mm with mm.
Notation "x =? y" := (sentence_eqb x y)%mm.

Fixpoint match_facts (Σ : Stack) (fact_hyps : list (string * Sentence)) : option Stack :=
  match Σ, fact_hyps with
  | [], [] => mret []
  | τ::Σ, (_, τ')::fact_hyps =>
    assert (τ =? τ')%mm ;; match_facts Σ fact_hyps
  | _, _ => mfail tt
  end.

Record Debug { Payload } := DEBUG {
  stack : Stack;
  unifier : Unifier;
  goal : Payload;
}.

Inductive error :=
  | UnificationFailed (d : @Debug (list (string * (string * string))))
  | MatchingFailed (d : @Debug (list (string * Sentence)))
  | StackUnderflow
  | StackOverflow
  | UndefinedType (id : string)
  | UndefinedFact (id : string)
  | UndefinedRule (id : string)
  | WrongStmt (τ : Sentence).

Inductive status :=
  | Error (e : error)
  | Assumed (τ : Sentence)
  | Proved (τ : Sentence).

Definition term (s : Statement) : Sentence :=
  match s with
  | Ax τ => τ
  | Th τ _ => τ
  end.

(* TODO: Error monad *)
Fixpoint exec_proof (F : File) (Σ : Stack) type_hyps fact_hyps proof :=
  match proof with
  | [] =>
    match Σ with
    | [] => Error StackUnderflow
    | [τ] => Proved τ
    | _ => Error StackOverflow
    end
  | TypeLbl lbl::proof =>
    match get type_hyps lbl with
    | Some (ty, var) => exec_proof F ([Cst ty; Var var]::Σ) type_hyps fact_hyps proof
    | None => Error (UndefinedType lbl)
    end
  | FactLbl lbl::proof =>
    match get fact_hyps lbl with
    | Some fact => exec_proof F (fact::Σ) type_hyps fact_hyps proof
    | None => Error (UndefinedFact lbl)
    end
  | RuleLbl lbl::proof =>
    match get (rules F) lbl with
    | Some (RULE r_type_hyps r_fact_hyps r_stmt) =>
        (* will instantiate the theorem `lbl` in the context *)
      match unify Σ [] r_type_hyps with
      | Some (Σ, unifier) => (* Σ has consumed all the argumetns for the theorem *)
        match match_facts Σ (inst r_fact_hyps unifier) with
        | Some Σ => exec_proof F ((term r_stmt).⟨unifier⟩::Σ) type_hyps fact_hyps proof
        | None => Error (MatchingFailed (DEBUG _ Σ unifier r_fact_hyps))
        end
      | None => Error (UnificationFailed (DEBUG _ Σ [] r_type_hyps))
      end
    | None => Error (UndefinedRule lbl)
    end
  end.

Definition check (F : File) (R : Rule) : status :=
  match statement R with
  | Ax stmt => Assumed stmt
  | Th stmt proof =>
    match exec_proof F [] (type_hypotheses R) (fact_hypotheses R) proof with
    | Proved stmt' =>
      if (stmt =? stmt')%mm then Proved stmt
      else Error (WrongStmt stmt')
    | status => status
    end
  end.

(*

[rule_1] ::=
  forall x : Var,
      wff x
      -----
      a x

PROOF:

----------------------            -------
[wffy : wff y] ⊢ wff y            [] ⊢ []
----------------------------------------- [rule_1]
           [wffy : wff y] ⊢ a y

*)

Example my_rule := RULE [("wffx", ("wff", "x"))]%string [] (Ax [Cst "a"; Var "x"]).
Example my_file := FILE [("rule_1", my_rule)]%string.
Example my_thm := RULE [("wffy", ("wff", "y"))]%string [] (Th [Cst "a"; Var "y"] [TypeLbl "wffy"; RuleLbl "rule_1"]).
Compute (check my_file my_thm).
Compute (unify [[Cst "wff"; Var "x"]] [] [("hyp1", ("wff", "y"))])%string.
