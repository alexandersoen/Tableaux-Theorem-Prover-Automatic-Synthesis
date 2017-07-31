Require Export a_base.
Set Implicit Arguments.

Module Type tableau_calculus_mod (X : base_mod).
Import X.

Inductive Tableau : Type :=
  | T : list PropF -> Tableau.

Inductive ClosedT_P : Tableau -> Prop :=
  | TBot   : forall L         , In ⊥ L                               -> ClosedT_P (T L)
  | TId    : forall L1 L2 L3 A, ClosedT_P (T (L1++A::L2++(A^c)::L3)) -> ClosedT_P (T (⊥::nil))
  | TAnd   : forall L1 L2 A B , ClosedT_P (T (L1++A∧B::L2))          -> ClosedT_P (T (L1++A::B::L2))
  | TOrL   : forall L1 L2 A B , ClosedT_P (T (L1++A∨B::L2))          -> ClosedT_P (T (L1++A::L2))
  | TOrR   : forall L1 L2 A B , ClosedT_P (T (L1++A∨B::L2))          -> ClosedT_P (T (L1++B::L2))
  | TImpL  : forall L1 L2 A B , ClosedT_P (T (L1++A→B::L2))          -> ClosedT_P (T (L1++¬A::L2))
  | TImpR  : forall L1 L2 A B , ClosedT_P (T (L1++A→B::L2))          -> ClosedT_P (T (L1++B::L2))
  | TNAndL : forall L1 L2 A B , ClosedT_P (T (L1++¬(A∧B)::L2))       -> ClosedT_P (T (L1++¬A::L2))
  | TNAndR : forall L1 L2 A B , ClosedT_P (T (L1++¬(A∧B)::L2))       -> ClosedT_P (T (L1++¬B::L2))
  | TNOr   : forall L1 L2 A B , ClosedT_P (T (L1++¬(A∨B)::L2))       -> ClosedT_P (T (L1++¬A::¬B::L2))
  | TNImp  : forall L1 L2 A B , ClosedT_P (T (L1++¬(A→B)::L2))       -> ClosedT_P (T (L1++A::¬B::L2))
.

End tableau_calculus_mod.