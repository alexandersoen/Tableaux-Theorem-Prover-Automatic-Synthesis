Require Export b_sequent_calculus c_tableau_calculus Omega.
Set Implicit Arguments.

Module Type equivalence_mod (X : base_mod) (Y : sequent_calculus_mod X) (Z : tableau_calculus_mod X).
Import X Y Z.

Lemma inListExists1 : forall A L, In A L -> (exists L', SetPropEq L (A::L')).
Proof.
  intros.
  induction L.
    contradict H.
    unfold SetPropEq.
    refine (ex_intro _ (a::L) _).
    intros. unfold iff; split.
    simpl. intros. destruct H0.
      refine (or_intror _); refine (or_introl _); assumption.
      refine (or_intror _); refine (or_intror _); assumption.
    simpl; intros; destruct H0.
      simpl in H; destruct H.
        rewrite H; refine (or_introl _); assumption.
        rewrite <- H0; refine (or_intror _); assumption.
      repeat assumption.
Qed.

Lemma SetEqAdd : forall A Γ Δ, SetPropEq Γ Δ -> SetPropEq (A::Γ) (A::Δ).
Proof.
  intros. unfold SetPropEq in *. intros.
  destruct (H A0).
  unfold iff; split.
    intros; simpl in *; destruct H2; auto; auto.
    intros; simpl in *; destruct H2; auto; auto.
Qed.

Lemma inListExists2 :
  forall A B L, In A L -> In B L -> (exists L', SetPropEq L (A::B::L')).
Proof.
  intros.
  induction L. contradiction H.
  destruct H, H0.
  rewrite <- H0; rewrite H.
  refine (ex_intro _ L _).
    unfold SetPropEq. intros. simpl. unfold iff. split.
      intros. refine (or_intror _). assumption.
      intros. destruct H1. repeat refine (or_introl _); assumption. assumption.
      
  rewrite H. refine (ex_intro _ L _).
    unfold SetPropEq; intros; simpl; unfold iff; split.
      intros. destruct H1. refine (or_introl _); assumption.
      refine (or_intror _); refine (or_intror _); assumption.
      intros. destruct H1. refine (or_introl _); assumption.
      destruct H1. refine (or_intror _); rewrite <- H1; assumption.
      auto.
  rewrite H0. refine (ex_intro _ L _).
    unfold SetPropEq; intros; simpl; unfold iff; split.
      intros. destruct H1. auto. auto. intros. destruct H1.
      rewrite <- H1; auto. assumption.
  pose (HS := IHL H H0). destruct HS.
  refine (ex_intro _ (a :: x) _).
  pose proof (SetEqAdd a H1) as H2.
  unfold SetPropEq in *; intros.
  pose (H2' := H2 A0). apply iff_sym in H2'.
    unfold iff in H2'; destruct H2'. unfold iff; split.
      intros. pose (H6 := H4 H5); simpl in *.
      destruct H6; auto; destruct H6; auto; destruct H6; auto; destruct H6; auto.
      intros. refine (H3 _). simpl in H5. simpl.
        destruct H5; auto; destruct H5; auto; destruct H5; auto; destruct H5; auto.
Qed.

Lemma SetPropEq_sym : forall Γ Δ, SetPropEq Γ Δ -> SetPropEq Δ Γ.
Proof.
  intros.
  unfold SetPropEq in *. intros. pose (H' := H A). apply iff_sym. assumption.
Qed.

Lemma SetPropEq_rewriteIn : forall A Γ Δ, In A Γ -> SetPropEq Γ Δ -> In A Δ.
Proof.
  intros. unfold SetPropEq in H0. pose (H0' := H0 A).
  unfold iff in H0'. destruct H0'. refine (H1 _). assumption.
Qed.

Lemma SetPropEq_trans : forall Γ Δ Σ,
  SetPropEq Γ Δ -> SetPropEq Δ Σ -> SetPropEq Γ Σ.
Proof.
  intros; unfold SetPropEq in *; unfold iff in *.
  intros; destruct (H A), (H0 A).
  split; auto; auto.
Qed.

Hint Resolve SetPropEq_trans SetPropEq_sym.

Lemma SetPropEq_app : forall Γ Δ, SetPropEq (Γ ++ Δ) (Δ ++ Γ).
Proof.
  intros; unfold SetPropEq; intros; unfold iff; split.
    intros.
      apply in_app_or in H; apply or_comm in H;
      apply in_or_app in H; assumption.
    intros.
      apply in_app_or in H; apply or_comm in H;
      apply in_or_app in H; assumption.
Qed.

Lemma SetPropEq_cons :
  forall Γ Δ A B, SetPropEq Γ (A::B::Δ) -> SetPropEq Γ (B::A::Δ).
Proof.
  unfold SetPropEq; intros; pose (H' := H A0).
  destruct H'; split.
    intros; pose (H3 := H0 H2); simpl in *.
    destruct H3; auto; destruct H3; auto; auto.
  intros; refine (H1 _); simpl in *.
    destruct H2; auto; destruct H2; auto; auto.
Qed.

Lemma SetPropEq_refl : forall Γ, SetPropEq Γ Γ.
Proof.
  intros; induction Γ.
    unfold SetPropEq; unfold iff; intros; auto.
    unfold SetPropEq; unfold iff; intros; auto.
Qed.

Lemma in_app_comm :
  forall (A : PropF) Γ Δ, In A (Γ ++ Δ) -> In A (Δ ++ Γ).
Proof.
  intros.
  apply in_app_iff; apply or_comm; apply in_app_iff; assumption.
Qed.

Theorem tableau_to_sequent_P : forall L (T : Tableau L),
  ClosedT_P T -> 
  (exists Γ Δ, (SetPropEq L (Γ ++ SetNegate Δ)) /\ (DerSeq_P (Γ ⇒ Δ))).
Proof.
  intros. destruct H. induction T.
    refine (ex_intro _ (Γ1 ++ A :: B :: Γ2) _).
    refine (ex_intro _ nil _). unfold SetNegate; simpl. split.
    pose proof (app_nil_r (Γ1 ++ A :: B :: Γ2)) as SL; rewrite SL.
    exact (SetPropEq_refl (Γ1 ++ A :: B :: Γ2)).
    constructor; assumption.
    
    refine (ex_intro _ (Γ1 ++ A :: Γ2) _).
    refine (ex_intro _ nil _). unfold SetNegate; simpl. split.
    pose proof (app_nil_r (Γ1 ++ A :: Γ2)) as SL; rewrite SL.
    exact (SetPropEq_refl (Γ1 ++ A :: Γ2)).
    constructor; assumption.
    
    refine (ex_intro _ (Γ1 ++ B :: Γ2) _).
    refine (ex_intro _ nil _). unfold SetNegate; simpl. split.
    pose proof (app_nil_r (Γ1 ++ B :: Γ2)) as SL; rewrite SL.
    exact (SetPropEq_refl (Γ1 ++ B :: Γ2)).
    constructor; assumption.
    
    refine (ex_intro _ (Γ1 ++ Γ2) _).
    refine (ex_intro _ (A::nil) _). unfold SetNegate; simpl. split.
    unfold SetPropEq. intros.
     unfold iff; intros; simpl in *; split.
      intros. refine ((in_or_app (Γ1++Γ2) (¬A::nil) A0) _).
      apply (in_app_or _ _ _) in H0. simpl in *.
      pose proof (in_app_iff Γ1 Γ2 A0) as HIn; rewrite HIn.
      apply (or_assoc _ _ _).
      pose proof (or_assoc (In A0 Γ2) (¬A=A0) False) as RW1;
      rewrite <- RW1.
      pose proof (or_comm (In A0 Γ2) (¬A=A0)) as Hcomm. rewrite Hcomm.
      apply (or_assoc _ _). refine (or_introl _). assumption.
      intros. apply (in_or_app _). apply (in_app_or _) in H0.
      pose proof (in_app_iff Γ1 Γ2 A0) as Happ.
      rewrite Happ in H0. simpl in *. apply (or_assoc _).
      apply (or_comm _). apply (or_assoc _).
      apply (or_assoc _) in H0. destruct H0.
      pose proof (or_comm (In A0 Γ2) (In A0 Γ1)) as Hcomm.
      rewrite Hcomm; assumption. contradict H0.
    constructor. apply (in_app_iff _) in H. apply (or_comm _) in H.
    apply (in_app_iff _) in H. simpl in H. destruct H.
    discriminate H. apply (in_app_iff _); apply (or_comm _);
    apply (in_app_iff); assumption.
    
    refine (ex_intro _ (Γ1 ++ B :: Γ2) _).
    refine (ex_intro _ (nil) _). unfold SetNegate; simpl. split.
    unfold SetPropEq. intros.
    unfold iff; intros; simpl in *; split.
      intros. refine ((in_or_app (Γ1++B::Γ2) (nil) A0) _).
      apply (in_app_or _ _ _) in H0. simpl in *.
      pose proof (in_app_iff Γ1 (B::Γ2) A0) as HIn; rewrite HIn.
      apply (or_assoc _ _ _). simpl.
      apply (or_assoc _). refine (or_introl _). assumption.
      intros.  pose (app_nil_r (Γ1 ++ B :: Γ2)) as Hsimp.
      rewrite Hsimp in H0; assumption.
    constructor. assumption.
    
    refine (ex_intro _ (Γ1++Γ2) _).
    refine (ex_intro _ (A::nil) _).
    unfold SetPropEq. intros.
    unfold iff; intros; simpl in *; split.
        intros. split.
          intros. unfold SetNegate; simpl.
          apply (in_app_iff _) in H0; apply (or_comm _) in H0;
          apply (in_app_iff _) in H0.
          apply (in_app_iff _); apply (or_comm); apply (in_app_iff _).
          simpl. simpl in H0. destruct H0. refine (or_introl _);
          assumption. refine (or_intror _).
          apply in_app_iff; apply or_comm; apply in_app_iff;
          assumption.
          intros. unfold SetNegate in H0; simpl in H0.
          apply in_app_comm in H0. simpl in H0.
          apply in_app_comm; simpl. destruct H0.
          refine (or_introl _); assumption.
          refine (or_intror _); apply in_app_comm; assumption.
    constructor. apply in_app_comm in H. simpl in H.
    destruct H. discriminate H. apply in_app_comm; assumption.
    
End equivalence_mod.