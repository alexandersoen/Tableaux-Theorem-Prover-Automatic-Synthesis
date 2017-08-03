Require Export a_base Bool.
Set Implicit Arguments.

Module Type sequent_calculus_mod (X : base_mod).
Import X.

Inductive Seq : Type :=
  | Arrow : list PropF -> list PropF -> Seq.

Notation "Γ ⇒ Δ" := (Arrow Γ Δ) (at level 80): My_scope.
(* To fix, turn inductive type wrt Seq *)

Inductive DerSeq_P : Seq -> Prop :=
  | SId   : forall A Γ Δ          , In A Γ                           -> In A Δ                        -> DerSeq_P (Γ ⇒ Δ)
  | SBot  : forall Γ Δ            , In ⊥ Γ                                                            -> DerSeq_P (Γ ⇒ Δ)
  | SAndL : forall A B Γ1 Γ2 Δ    , DerSeq_P (Γ1++A::B::Γ2 ⇒ Δ)                                       -> DerSeq_P (Γ1++A∧B::Γ2 ⇒ Δ)
  | SAndR : forall A B Γ Δ1 Δ2    , DerSeq_P (Γ ⇒ Δ1++A::Δ2)         -> DerSeq_P (Γ ⇒ Δ1++B::Δ2)      -> DerSeq_P (Γ ⇒ Δ1++A∧B::Δ2)
  | SOrL  : forall A B Γ1 Γ2 Δ    , DerSeq_P (Γ1++A::Γ2 ⇒ Δ)         -> DerSeq_P (Γ1++B::Γ2 ⇒ Δ)      -> DerSeq_P (Γ1++A∨B::Γ2 ⇒ Δ)
  | SOrR  : forall A B Γ Δ1 Δ2    , DerSeq_P (Γ ⇒ Δ1++A::B::Δ2)                                       -> DerSeq_P (Γ ⇒ Δ1++A∨B::Δ2)
  | SImpL : forall A B Γ1 Γ2 Δ1 Δ2, DerSeq_P (Γ1++B::Γ2 ⇒ Δ1++Δ2)    -> DerSeq_P (Γ1++Γ2 ⇒ Δ1++A::Δ2) -> DerSeq_P (Γ1++A→B::Γ2 ⇒ Δ1++Δ2)
  | SImpR : forall A B Γ1 Γ2 Δ1 Δ2, DerSeq_P (Γ1++A::Γ2 ⇒ Δ1++B::Δ2)                                  -> DerSeq_P (Γ1++Γ2 ⇒ Δ1++A→B::Δ2)
  .

Check DerSeq_P.

Theorem test : forall A, DerSeq_P (A::nil ⇒ A::nil).
Proof.
  intros.
  apply (SId A). intuition. intuition.
Qed.

End sequent_calculus_mod.