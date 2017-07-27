Require Export a_base.
Set Implicit Arguments.

Module Type tableau_calculus_mod (X : base_mod).
Import X.

Inductive Tableau : list PropF -> Prop :=
| TAnd : forall X A B, Tableau (A∧B::X) -> Tableau (A::B::X)
| TOrL : forall X A B, Tableau (A∨B::X) -> Tableau (A::X)
| TOrR : forall X A B, Tableau (A∨B::X) -> Tableau (B::X)
| TImpL : forall X A B, Tableau (A→B::X) -> Tableau (¬A::X)
| TImpR : forall X A B, Tableau (A→B::X) -> Tableau (B::X)
.

Definition IsClosed T := or (exists A, In A T -> In (¬A) T) (In ⊥ T).

Print IsClosed.

End tableau_calculus_mod.