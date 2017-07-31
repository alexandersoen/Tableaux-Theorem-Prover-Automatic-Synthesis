Require Export b_sequent_calculus c_tableau_calculus Omega.
Set Implicit Arguments.

Module Type equivalence_mod
  (X : base_mod) (Y : sequent_calculus_mod X)
  (Z : tableau_calculus_mod X).
Import X Y Z.

Lemma inListExists1 : forall A L, In A L ->
  (exists L', SetPropEq L (A::L')).
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
      intros. destruct H1. repeat refine (or_introl _); assumption.
      assumption.
      
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
      destruct H6; auto; destruct H6; auto; destruct H6; auto;
      destruct H6; auto.
      intros. refine (H3 _). simpl in H5. simpl.
        destruct H5; auto; destruct H5; auto; destruct H5; auto;
        destruct H5; auto.
Qed.

Lemma SetPropEq_sym : forall Γ Δ, SetPropEq Γ Δ -> SetPropEq Δ Γ.
Proof.
  intros.
  unfold SetPropEq in *. intros. pose (H' := H A). apply iff_sym.
  assumption.
Qed.

Lemma SetPropEq_rewriteIn1 : forall A Γ Δ, In A Γ -> SetPropEq Γ Δ
  -> In A Δ.
Proof.
  intros. unfold SetPropEq in H0. pose (H0' := H0 A).
  unfold iff in H0'. destruct H0'. refine (H1 _). assumption.
Qed.

Lemma SetPropEq_rewriteIn2 : forall A Γ Δ, SetPropEq Γ Δ
  -> In A Γ -> In A Δ.
Proof.
  intros. unfold SetPropEq in H; unfold iff in H.
  pose (H' := H A); destruct H'.
  exact (H1 H0).
Qed.

Lemma SetPropEq_trans : forall Γ Δ Σ,
  SetPropEq Γ Δ -> SetPropEq Δ Σ -> SetPropEq Γ Σ.
Proof.
  intros; unfold SetPropEq in *; unfold iff in *.
  intros; destruct (H A), (H0 A).
  split; auto; auto.
Qed.

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

Lemma SetPropEq_rewrite1 : forall L x y z,
  SetPropEq L (x ++ y) -> SetPropEq x z -> SetPropEq L (z ++ y).
Proof.
  intros. unfold SetPropEq in *; unfold iff in *; intros.
  pose (H' := H A); pose (H0' := H0 A);
  destruct H'; destruct H0'; split.
    intros. pose (H6 := H1 H5).
    apply in_app_iff. apply in_app_iff in H6.
    destruct H6.
      refine (or_introl _); exact (H3 H6).
      refine (or_intror _); assumption.
    intros. apply in_app_iff in H5. refine (H2 _).
    apply in_app_iff. destruct H5.
      refine (or_introl _); exact (H4 H5).
      refine (or_intror _); assumption.
Qed.

Lemma SetPropEq_rewrite2 : forall L x y z, SetPropEq L (x ++ SetNegate y)
  -> SetPropEq y z -> SetPropEq L (x ++ SetNegate z).
Proof.
  intros. unfold SetPropEq in *;
  unfold iff in *; intros.
  pose (H' := H A); destruct H'. split.
    intros. apply in_app_iff. pose (H4 := H1 H3).
    apply in_app_iff in H4; destruct H4.
    refine (or_introl _); assumption.
    refine (or_intror _). unfold SetNegate in H4.
    rewrite (in_map_iff (fun p => ¬p) y A) in H4.
    destruct H4. destruct H4. rewrite <- H4.
    pose (H0' := H0 x0); destruct H0'.
    pose (H8 := H6 H5).
    apply (in_map (fun p => ¬p) _ _) in H8.
    unfold SetNegate; assumption.

    intros. refine (H2 _). apply in_app_iff.
    apply in_app_iff in H3. destruct H3.
    refine (or_introl _); assumption.
    refine (or_intror _).
    rewrite (in_map_iff (fun p => ¬p) z A) in H3.
    destruct H3. destruct H3. rewrite <- H3.
    pose (H0' := H0 x0); destruct H0'.
    pose (H7 := H6 H4).
    apply (in_map (fun p => ¬p) _ _) in H7.
    unfold SetNegate; assumption.
Qed.

Lemma SetPropEq_rewrite3 : forall L x0 x1 y0 y1,
  SetPropEq L (x0 ++ SetNegate y0) -> SetPropEq x0 x1
  -> SetPropEq y0 y1 -> SetPropEq L (x1 ++ SetNegate y1).
Proof.
  intros. pose (H2 := SetPropEq_rewrite1 _ H H0).
  pose (H3 := SetPropEq_rewrite2 _ H2 H1).
  assumption.
Qed.

Theorem tableau_to_sequent_P : forall L,
  ClosedT_P L -> 
  (exists Γ Δ, (SetPropEq L (Γ ++ SetNegate Δ)) /\ (DerSeq_P (Γ ⇒ Δ))).
Proof.
  intros. destruct H.
    assert (H1 := (inListExists2 A _ _) H H0); destruct H1.
    refine (ex_intro _ (A::x) _);
    refine (ex_intro _ (A::nil) _);
    simpl; split.
      unfold SetPropEq in *; unfold iff in *; intros;
      assert (H2 := H1 A0); destruct H2; split; intros; simpl in *;
      repeat (rewrite in_app_iff in *; simpl in *); intuition.
    apply (SId A); simpl; auto.
    
    apply TAnd in H.
    refine (ex_intro _ (L1 ++ A ∧ B :: L2) _);
    refine (ex_intro _ (nil) _);
    simpl; split.
      rewrite app_nil_r; exact (SetPropEq_refl _).
    
Admitted.

Theorem sequent_to_tableau_P : forall L,
  (exists Γ Δ, (SetPropEq L (Γ ++ SetNegate Δ)) /\ (DerSeq_P (Γ ⇒ Δ)))
  -> ClosedT_P L.
Proof.
Admitted.

End equivalence_mod.