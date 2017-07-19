(* Imports *)
Require Import Bool.
Require Import List.

(* The basic definition as stated in the paper *)
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
Notation "¬ A" := (Neg A) (at level 5).
Definition Top := ¬ ⊥.
Notation "⊤" := Top (at level 0).

(* Define a evaluation function which accepts a map from
  propositional variables to booleans and a PropF
  - TrueQ in the paper *)
Fixpoint TrueQ (var_map : PropVars -> bool) (A : PropF) := match A with
  | # P => var_map P
  | ⊥ => false
  | B ∧ C => (TrueQ var_map B) && (TrueQ var_map C)
  | B ∨ C => (TrueQ var_map B) || (TrueQ var_map C)
  | B → C => (negb (TrueQ var_map B)) || (TrueQ var_map C)
end.
Definition Satisfies v Γ := forall A, In A Γ -> (Is_true (TrueQ v A)).
Definition Models Γ A := forall v, Satisfies v Γ -> (Is_true (TrueQ v A)).
Notation "Γ ⊨ A" := (Models Γ A) (at level 80).
Definition Valid A := nil ⊨ A.

Theorem test : (forall P : PropF, Valid (P → P)).
Proof.
  intros P.
  unfold Valid.
  unfold Models.
  intros v.
  unfold Satisfies.
  simpl.
  intros.
  case (TrueQ v P).
    simpl.
    exact I.
    
    simpl.
    exact I.
Qed.

Theorem test2 : (forall P Q: PropF, Valid (P → Q → P)).
Proof.
  intros.
  unfold Valid. unfold Models.
  intros.
  simpl.
  case (TrueQ v P).
    simpl.
    case (TrueQ v Q).
      simpl.
      exact I.
      
      simpl.
      exact I.
    
    simpl.
    exact I.
Qed.