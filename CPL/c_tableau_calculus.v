Require Export a_base Omega.
Set Implicit Arguments.

Module Type tableau_calculus_mod (X : base_mod).
Import X.

Definition Tableau := list PropF.

Inductive Result :=
  | closed : Result
  | open : Result.

Fixpoint AndRuleTAcc (T : Tableau) (Acc : Tableau) : list Tableau :=
  match T with
  | nil => Acc :: nil
  | x :: xs =>
    match x with
    | A ∧ B => (A :: B :: xs ++ Acc) :: nil
    | _ => AndRuleTAcc xs (x :: Acc)
    end
  end.

Fixpoint OrRuleTAcc (T : Tableau) (Acc : Tableau) : list Tableau :=
  match T with
  | nil => Acc :: nil
  | x :: xs =>
    match x with
    | A ∨ B => (A :: xs ++ Acc) :: (B :: xs ++ Acc) :: nil
    | _ => AndRuleTAcc xs (x :: Acc)
    end
  end.

Fixpoint AndRuleT (T : Tableau) := AndRuleTAcc T nil.
Fixpoint OrRuleT (T : Tableau) := OrRuleTAcc T nil.

Reserved Notation "A ⊢T Δ" (at level 80).

(*

Inductive TRule : Tableau -> Tableau -> Prop :=
| TAnd : forall A B Γ1 Γ2,
    (Γ1 ++ A ∧ B :: Γ2) ⊢T (Γ1 ++ A :: B :: Γ2)
| TOrl : forall A B Γ1 Γ2,
    (Γ1 ++ A ∨ B :: Γ2) ⊢T (Γ1 ++ A :: Γ2)
| TOrr : forall A B Γ1 Γ2,
    (Γ1 ++ A ∨ B :: Γ2) ⊢T (Γ1 ++ B :: Γ2)
where "A ⊢T Δ" := (TRule A Δ) : My_scope.

Definition ClosedT (T : Tableau) :=
  (In ⊥ T) \/ (exists A, In A T -> In (¬ A) T).

*)

Inductive TRule : Tableau -> list Tableau -> Prop :=
| TAnd : forall A B Γ1 Γ2,
    (Γ1 ++ A ∧ B :: Γ2) ⊢T ((Γ1 ++ A :: B :: Γ2) :: nil)
| TOr : forall A B Γ1 Γ2,
    (Γ1 ++ A ∨ B :: Γ2) ⊢T ((Γ1 ++ A :: Γ2) :: (Γ1 ++ B :: Γ2) :: nil)
where "A ⊢T Δ" := (TRule A Δ) : My_scope.

Fixpoint size (F : PropF) : nat :=
  match F with
  | # P => 0
  | ⊥ => 0
  | A ∨ B => S (size A + size B)
  | A ∧ B => S (size A + size B)
  | A → B => S (size A + size B)
end.

Fixpoint foldr (A B : Type) (f : A -> B -> B) acc l :=
  match l with
  | nil => acc
  | x :: xs => foldr f (f x acc) xs
end.

Definition tsize (T : Tableau) := foldr (fun x y => size x + y) 0 T.

Compute (tsize (⊥ → ⊥ :: ⊥ :: ⊥ ∨ ⊥ :: nil)).

Definition NClosed (T : Tableau) := (In ⊥ T) \/ (exists A, In A T -> In (¬ A) T).

Definition rOrder (t1 t2 : Tableau) :=
  tsize t1 < tsize t2.

Print Acc.

Lemma rOrder_wf' : forall len, forall t,
  tsize t <= len -> Acc rOrder t.
  Proof.
    unfold rOrder.
    induction len.
      intros.
      induction t.
        unfold tsize in H; simpl in H.
        constructor.
          intros.
          contradict H0; unfold tsize; simpl; omega.
        unfold tsize in H. simpl in H.

Lemma rOrder_wf : well_founded rOrder.
  Proof.
    red. intros. 

Fixpoint TClosed (T : Tableau) : Prop :=
  NClosed T \/
  (exists TC, forall B, T ⊢T TC -> In B TC -> TClosed B).

Fixpoint oneOf (T : Tableau) (f : PropF -> Tableau -> Prop) :=
  match T with
  | nil => False
  | x :: xs => or (f x T) (oneOf xs f)
  end.

Fixpoint tMinus (E : PropF) (T : Tableau) : Tableau :=
  match T with
  | nil => nil
  | x :: xs =>
    match (x = E) with
    | True => xs
    | False => x :: (tMinus E xs)
    end
  end.

Fixpoint 

Compute (oneOf (⊥ :: nil) In).

Definition Absurdity (T : Tableau) := (exists A, and (In A T) (In (¬A) T)) = True.

Fixpoint isClosed (T : Tableau) : Result :=
  match Absurdity T with
  | True => closed
  end.

End tableau_calculus_mod.