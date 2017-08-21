Require Export List Bool.
Set Implicit Arguments.

Module Type base_mod.

(* Defines the logical symbols *)

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

(* Test extraction *)
Definition isBot x := if Varseq_dec x ⊥ then true else false.

End base_mod.