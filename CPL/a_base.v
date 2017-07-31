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

Definition Complement (P : PropF) : PropF :=
  match P with
  | (A → ⊥) => A
  | A => ¬ A
  end.

Notation "A ^c" := (Complement A) (at level 2) : My_scope.

Fixpoint map_fold_right (A B:Type) (f : B -> A) (g : A -> A -> A) a l := match l with
 | nil => a
 | b::l2 => g (f b) (map_fold_right f g a l2)
end.

Fixpoint TrueQ v A : bool := match A with
 | # P   => v P
 | ⊥     => false
 | B ∨ C => (TrueQ v B) || (TrueQ v C)
 | B ∧ C => (TrueQ v B) && (TrueQ v C)
 | B → C => (negb (TrueQ v B)) || (TrueQ v C)
end.
Definition Satisfies v Γ := forall A, In A Γ -> Is_true (TrueQ v A).
Definition Models Γ A := forall v,Satisfies v Γ->Is_true (TrueQ v A).
Notation "Γ ⊨ A" := (Models Γ A) (at level 80).
Definition Valid A := nil ⊨ A.

Compute (1 :: 2 :: nil = 2 :: 1 :: nil).

Definition SetPropEq (l1 l2 : list PropF) := (forall A, In A l1 <-> In A l2).

Definition SetNegate (l : list PropF) := map (fun p => ¬p) l.

End base_mod.