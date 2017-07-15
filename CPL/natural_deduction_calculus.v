(*Require Import Utf8.*)

Parameter PropVars : Set.
Hypothesis Varseq_dec : forall x y : PropVars, {x = y} + {x <> y}.

Inductive PropF : Set :=
  | Var : PropVars -> PropF
  | Bot : PropF
  | Conj : PropF -> PropF -> PropF
  | Disj : PropF -> PropF -> PropF
  | Impl : PropF -> PropF -> PropF
.
Notation "# P" := (Var P) (at level 1).
Notation "A ∨ B" := (Disj A B) (at level 15, right associativity).
Notation "A ∧ B" := (Conj A B) (at level 15, right associativity).
Notation "A → B" := (Impl A B) (at level 16, right associativity).
Notation "⊥" := Bot (at level 0).
Definition Neg A := A → ⊥.
