Require Export a_base.
Set Implicit Arguments.

Module Type sequent_calculus_mod (X : base_mod).
Import X.

Inductive Seq : Type :=
  | Arrow : list PropF -> list PropF -> Seq.

Notation "Γ ⇒ Δ" := (Arrow Γ Δ) (at level 80): My_scope.

Inductive DerSeq : Seq -> Prop :=
  | SId   : forall A Γ Δ      , In A Γ                    -> In (¬A) Δ              -> DerSeq (Γ ⇒ Δ)
  | SBot  : forall Γ Δ        , In ⊥ Γ                                              -> DerSeq (Γ ⇒ Δ)
  | SAndL : forall A B Γ1 Γ2 Δ, DerSeq (Γ1++A::B::Γ2 ⇒ Δ)                           -> DerSeq (Γ1++A∧B::Γ2 ⇒ Δ)
  | SAndR : forall A B Γ Δ1 Δ2, DerSeq (Γ ⇒ Δ1++A::Δ2)    -> DerSeq (Γ ⇒ Δ1++B::Δ2) -> DerSeq (Γ ⇒ Δ1++A∧B::Δ2)
  | SOrL  : forall A B Γ1 Γ2 Δ, DerSeq (Γ1++A::Γ2 ⇒ Δ)    -> DerSeq (Γ1++B::Γ2 ⇒ Δ) -> DerSeq (Γ1++A∨B::Γ2 ⇒ Δ)
  | SOrR  : forall A B Γ Δ1 Δ2, DerSeq (Γ ⇒ Δ1++A::B::Δ2)                           -> DerSeq (Γ ⇒ Δ1++A∨B::Δ2)
  | SImpL : forall A B Γ1 Γ2 Δ, DerSeq (Γ1++B::Γ2 ⇒ Δ)    -> DerSeq (Γ1++Γ2 ⇒ A::Δ) -> DerSeq (Γ1++A→B::Γ2 ⇒ Δ)
  | SImpR : forall A B Γ Δ1 Δ2, DerSeq (A::Γ ⇒ Δ1++B::Δ2)                           -> DerSeq (Γ ⇒ Δ1++A→B::Δ2)
  .



End sequent_calculus_mod.