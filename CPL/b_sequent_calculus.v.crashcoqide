Require Export a_base Bool.
Set Implicit Arguments.

Module Type sequent_calculus_mod (X : base_mod).
Import X.

Reserved Notation "Γ ==> A" (at level 80).

Inductive G : list PropF -> list PropF -> Prop :=
| Gax  : forall A Γ Δ      , In A Γ              -> In A Δ           -> Γ ==> Δ
| GBot : forall Γ Δ        , In ⊥ Γ                                  -> Γ ==> Δ
| AndL : forall A B Γ1 Γ2 Δ, Γ1++A::B::Γ2 ==> Δ                      -> Γ1++A∧B::Γ2 ==> Δ
| AndR : forall A B Γ Δ1 Δ2, Γ ==> Δ1++A::Δ2     -> Γ ==> Δ1++B::Δ2  -> Γ ==> Δ1++A∧B::Δ2
| OrL  : forall A B Γ1 Γ2 Δ, Γ1++A::Γ2 ==> Δ     -> Γ1++B::Γ2 ==> Δ  -> Γ1++A∨B::Γ2 ==> Δ
| OrR  : forall A B Γ Δ1 Δ2, Γ ==> Δ1++A::B::Δ2                      -> Γ ==> Δ1++A∨B::Δ2
| ImpL : forall A B Γ1 Γ2 Δ, Γ1++B::Γ2 ==> Δ     -> Γ1++Γ2 ==> A::Δ  -> Γ1++A→B::Γ2 ==> Δ
| ImpR : forall A B Γ Δ1 Δ2, A::Γ ==> Δ1++B::Δ2                      -> Γ ==> Δ1++A→B::Δ2
| Cut  : forall A Γ Δ      , Γ ==> A::Δ          -> A::Γ ==> Δ       -> Γ ==> Δ
where "Γ ==> Δ" := (G Γ Δ) : My_scope.

Check forall Γ Δ, exists A, In A Γ -> In A Δ -> True.

Inductive Seq : Type :=
| Arrow : list PropF -> list PropF -> Seq.

Notation "Γ ⇒ Δ" := (Arrow Γ Δ) (at level 80): My_scope.
(* To fix, turn inductive type wrt Seq *)

Inductive DerSeq_P : Seq -> Prop :=
 | SId   : forall A Γ Δ      , In A Γ                      -> In A Δ                     -> DerSeq_P (Γ ⇒ Δ)
 | SBotL : forall Γ Δ        , In ⊥ Γ                                                    -> DerSeq_P (Γ ⇒ Δ)
 | SAndL : forall A B Γ1 Γ2 Δ, DerSeq_P (Γ1++A::B::Γ2 ⇒ Δ)                               -> DerSeq_P (Γ1++A∧B::Γ2 ⇒ Δ)
 | SAndR : forall A B Γ Δ1 Δ2, DerSeq_P (Γ ⇒ Δ1++A::Δ2)    -> DerSeq_P (Γ ⇒ Δ1++B::Δ2)   -> DerSeq_P (Γ ⇒ Δ1++A∧B::Δ2)
 | SOrL  : forall A B Γ1 Γ2 Δ, DerSeq_P (Γ1++A::Γ2 ⇒ Δ)    -> DerSeq_P (Γ1++B::Γ2 ⇒ Δ)   -> DerSeq_P (Γ1++A∨B::Γ2 ⇒ Δ)
 | SOrR  : forall A B Γ Δ1 Δ2, DerSeq_P (Γ ⇒ Δ1++A::B::Δ2)                               -> DerSeq_P (Γ ⇒ Δ1++A∨B::Δ2)
 | SImpL : forall A B Γ1 Γ2 Δ, DerSeq_P (Γ1++B::Γ2 ⇒ Δ)    -> DerSeq_P (Γ1++Γ2 ⇒ A::Δ)   -> DerSeq_P (Γ1++A→B::Γ2 ⇒ Δ)
 | SImpR : forall Γ Δ1 Δ2 A B, DerSeq_P (A::Γ ⇒ Δ1++B::Δ2)                               -> DerSeq_P (Γ ⇒ Δ1++A→B::Δ2).

End sequent_calculus_mod.