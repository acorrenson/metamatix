From Coq Require Import String List.
Import ListNotations.

Inductive Symbol :=
  | Var (v : string)
  | Cst (c : string).

Definition Sentence := list Symbol.

(* Substitute all variables by their projection under σ *)
Fixpoint substitute (τ : Sentence) (σ : string -> Sentence) : Sentence :=
  match τ with
  | [] => []
  | Var v::τ => (σ v) ++ (substitute τ σ)
  | x::τ => x::(substitute τ σ)
  end.
Notation "τ '⟨' σ '⟩'" := (substitute τ σ) (at level 80).
Notation "x ∈ L" := (In x L) (at level 80).

Definition mbind [A B] (m : option A) (f : A -> option B) : option B :=
  match m with
  | Some a => f a
  | None   => None
  end.

Definition mret  [A] (a : A)    : option A := Some a.
Definition mfail [A] (u : unit) : option A := None.
Definition assert (b : bool)    := if b then Some tt else None.
Definition unless (b : bool)    := assert (negb b).

Notation "a <- x ;; y" := (mbind x (fun a => y)) (at level 80).
Notation "x ;; y" := (mbind x (fun _ => y)) (at level 80).
