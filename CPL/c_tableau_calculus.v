Require Export a_base.
Set Implicit Arguments.

Module Type tableau_calculus_mod (X : base_mod).
Import X.

Inductive Tableau : list PropF -> Type :=
  | TAnd   : forall Γ1 Γ2 A B , Tableau (Γ1++A∧B::Γ2)    -> Tableau (Γ1++A::B::Γ2)
  | TOrL   : forall Γ1 Γ2 A B , Tableau (Γ1++A∨B::Γ2)    -> Tableau (Γ1++A::Γ2)
  | TOrR   : forall Γ1 Γ2 A B , Tableau (Γ1++A∨B::Γ2)    -> Tableau (Γ1++B::Γ2)
  | TImpL  : forall Γ1 Γ2 A B , Tableau (Γ1++A→B::Γ2)    -> Tableau (Γ1++¬A::Γ2)
  | TImpR  : forall Γ1 Γ2 A B , Tableau (Γ1++A→B::Γ2)    -> Tableau (Γ1++B::Γ2)
  | TNAndL : forall Γ1 Γ2 A B , Tableau (Γ1++¬(A∧B)::Γ2) -> Tableau (Γ1++¬A::Γ2)
  | TNAndR : forall Γ1 Γ2 A B , Tableau (Γ1++¬(A∧B)::Γ2) -> Tableau (Γ1++¬B::Γ2)
  | TNOr   : forall Γ1 Γ2 A B , Tableau (Γ1++¬(A∨B)::Γ2) -> Tableau (Γ1++¬A::¬B::Γ2)
  | TNImp  : forall Γ1 Γ2 A B , Tableau (Γ1++¬(A→B)::Γ2) -> Tableau (Γ1++A::¬B::Γ2)
  | TBotL  : forall Γ1 Γ2 Γ3 A, Tableau (Γ1++A::nil++Γ2++¬A::nil++Γ3) -> Tableau (⊥::nil)
  | TBotR  : forall Γ1 Γ2 Γ3 A, Tableau (Γ1++¬A::nil++Γ2++A::nil++Γ3) -> Tableau (⊥::nil).

Inductive ClosedT_P Γ (T : Tableau Γ) : Prop :=
  | Closed : In ⊥ Γ -> ClosedT_P T.

End tableau_calculus_mod.