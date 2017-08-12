Require Export List Bool.
Set Implicit Arguments.

Module Type base_mod.

Delimit Scope My_scope with M.
Open Scope My_scope.

Parameter PropVars : Set.
Axiom Varseq_dec : forall x y:PropVars, {x = y} + {x <> y}.

Inductive PropF : Set :=
 | Var : PropVars -> PropF
 | Bot : PropF
 | Conj : PropF -> PropF -> PropF
 | Disj : PropF -> PropF -> PropF
 | Impl : PropF -> PropF -> PropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A ∨ B" := (Disj A B) (at level 15, right associativity) : My_scope.
Notation "A ∧ B" := (Conj A B) (at level 15, right associativity) : My_scope.
Notation "A → B" := (Impl A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.
Definition Neg A := A → ⊥.
Notation "¬ A" := (Neg A) (at level 5) : My_scope.
Definition Top := ¬⊥.
Notation "⊤" := Top (at level 0) : My_scope.
Definition BiImpl A B := (A→B)∧(B→A).
Notation "A ↔ B" := (BiImpl A B) (at level 17, right associativity) : My_scope.

Axiom consistent : forall A, A <> ¬A.

Fixpoint connectives (P : PropF) : nat :=
  match P with
  | Var x => 0
  | Bot => 0
  | Conj x y => 1 + (connectives x) + (connectives y)
  | Disj x y => 1 + (connectives x) + (connectives y)
  | Impl x y => 1 + (connectives x) + (connectives y)
  end.

Fixpoint grade (P : list PropF) : nat :=
  match P with
  | nil => 0
  | x::xs => connectives x + grade xs
  end.

Axiom PropF_decidable : forall A B : PropF, A=B \/ A<>B.

End base_mod.