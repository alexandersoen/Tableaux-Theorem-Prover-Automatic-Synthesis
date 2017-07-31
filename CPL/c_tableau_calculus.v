Require Export a_base.
Set Implicit Arguments.

Module Type tableau_calculus_mod (X : base_mod).
Import X.

Definition Tableau : Type := list PropF.

Inductive ClosedT_P : Tableau -> Prop :=
  | TId    : forall L A       , In A L -> In (¬A) L                  -> ClosedT_P L
  | TAnd   : forall L1 L2 A B , ClosedT_P (L1++A::B::L2) -> ClosedT_P (L1++A∧B::L2)
  | TOr    : forall L1 L2 A B , ClosedT_P (L1++A::L2) -> ClosedT_P (L1++B::L2) -> ClosedT_P (L1++A∨B::L2)
  | TImp   : forall L1 L2 A B , ClosedT_P (L1++¬A::L2) -> ClosedT_P (L1++B::L2) -> ClosedT_P (L1++A→B::L2)
  | TNAnd  : forall L1 L2 A B , ClosedT_P (L1++¬A::L2) -> ClosedT_P (L1++¬B::L2) -> ClosedT_P (L1++¬(A∧B)::L2)
  | TNOr   : forall L1 L2 A B , ClosedT_P (L1++¬A::¬B::L2) -> ClosedT_P (L1++¬(A∨B)::L2)
  | TNImp  : forall L1 L2 A B , ClosedT_P (L1++A::¬B::L2) -> ClosedT_P (L1++¬(A→B)::L2)
.

End tableau_calculus_mod.