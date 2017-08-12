Require Export b_sequent_calculus c_tableau_calculus Omega.
Set Implicit Arguments.

Module Type equivalence_mod
  (X : base_mod) (Y : sequent_calculus_mod X)
  (Z : tableau_calculus_mod X).
Import X Y Z.

Definition tuple_app (A B : list PropF * list PropF) :=
  (fst A ++ fst B, snd A ++ snd B).

Notation "A ++_ B" := (tuple_app A B)
  (at level 80, right associativity) : My_scope.

Fixpoint node_split (L : Tableau) :=
  match L with
  | nil => (nil, nil)
  | x::xs => match x with
             | x → ⊥ => (nil, x::nil) ++_ (node_split xs)
             | x => (x::nil, nil) ++_ (node_split xs)
             end
  end.

(* Fixpoint node_split_help (L : Tableau) (Γ Δ : list PropF) :=
  match L with
  | nil => (Γ, Δ)
  | x::xs => match x with
             | x → ⊥ => node_split_help xs Γ (Δ++x::nil)
             | x  => node_split_help xs (Γ++x::nil) Δ
             end
  end.

Definition node_split L := (node_split_help L nil nil). *)

Lemma fst_snd_node_split : forall A,
  node_split A = (fst (node_split A), snd (node_split A)).
Proof.
  intros. induction A.
    unfold node_split; simpl; trivial.
    case a; intros; simpl; rewrite IHA; unfold tuple_app; simpl; trivial.
    case p0; intros; simpl; trivial.
Qed.

Lemma tuple_list_app : forall A B,
  node_split (A ++ B) = ((node_split A) ++_ (node_split B)).
Proof.
  intros. unfold tuple_app. induction A, B.
    unfold node_split; unfold tuple_app; simpl; trivial.
    
    rewrite app_nil_l; simpl (node_split nil);
    simpl (fst (nil, nil)); simpl (snd (nil, nil)); rewrite app_nil_l;
    rewrite <- fst_snd_node_split; trivial.
    
    rewrite app_nil_r; simpl (node_split nil);
    simpl (fst (nil, nil)); simpl (snd (nil, nil)); repeat rewrite app_nil_r;
    rewrite <- fst_snd_node_split; trivial.
    
    case a; simpl (node_split (_ :: A));
    simpl (node_split ((_ :: A) ++ p :: B));
    intros; rewrite IHA; unfold tuple_app; simpl; trivial.
      case p1; intros; unfold tuple_app; simpl; trivial.
Qed.

Lemma node_split_split : forall L,
  exists A B, node_split L = (A, B).
Proof.
  intros; induction L.
    repeat refine (ex_intro _ nil _); simpl; trivial.
    destruct IHL; destruct H. case a; intros.
      refine (ex_intro _ (# p :: x) _);
      refine (ex_intro _ (x0) _).
      simpl; rewrite H; unfold tuple_app; simpl; trivial.
      
      refine (ex_intro _ (⊥ :: x) _);
      refine (ex_intro _ (x0) _).
      simpl; rewrite H; unfold tuple_app; simpl; trivial.
      
      refine (ex_intro _ (p ∧ p0 :: x) _);
      refine (ex_intro _ (x0) _).
      simpl; rewrite H; unfold tuple_app; simpl; trivial.
      
      refine (ex_intro _ (p ∨ p0 :: x) _);
      refine (ex_intro _ (x0) _).
      simpl; rewrite H; unfold tuple_app; simpl; trivial.
      
      case p0; intros.
        refine (ex_intro _ (p → # p1 :: x) _);
        refine (ex_intro _ (x0) _).
        simpl; rewrite H; unfold tuple_app; simpl; trivial.
        
        refine (ex_intro _ (x) _);
        refine (ex_intro _ (p :: x0) _).
        simpl; rewrite H; unfold tuple_app; simpl; trivial.
        
        refine (ex_intro _ (p → p1 ∧ p2 :: x) _);
        refine (ex_intro _ (x0) _).
        simpl; rewrite H; unfold tuple_app; simpl; trivial.
        
        refine (ex_intro _ (p → p1 ∨ p2 :: x) _);
        refine (ex_intro _ (x0) _).
        simpl; rewrite H; unfold tuple_app; simpl; trivial.
        
        refine (ex_intro _ (p → p1 → p2 :: x) _);
        refine (ex_intro _ (x0) _).
        simpl; rewrite H; unfold tuple_app; simpl; trivial.
Qed.

Definition tuple_to_seq (N : list PropF * list PropF) :=
  fst N ⇒ snd N.

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

Lemma in_split2 : forall (L : list PropF) A B,
  A <> B -> In A L -> In B L -> 
    ((exists L1 L2 L3, L = L1++A::L2++B::L3) \/
    (exists L1 L2 L3, L = L1++B::L2++A::L3)).
Proof.
  intros L A B neg.
  intros. induction L. contradiction H. simpl in *.
  destruct H, H0.
    repeat refine (or_intror _). refine (ex_intro _ nil _).
    refine (ex_intro _ L _). rewrite <- H in neg. rewrite <- H0 in neg.
    intuition.
    
    rewrite H. apply in_split in H0; destruct H0; destruct H0.
    rewrite H0.
    refine (or_introl _). refine (ex_intro _ nil _).
    refine (ex_intro _ x _). refine (ex_intro _ x0 _). intuition.
    
    rewrite H0. apply in_split in H; destruct H; destruct H.
    rewrite H.
    refine (or_intror _). refine (ex_intro _ nil _).
    refine (ex_intro _ x _). refine (ex_intro _ x0 _). intuition.
    
    destruct (IHL H H0). destruct H1. destruct H1. destruct H1.
    rewrite H1.
    refine (or_introl _).
    refine (ex_intro _ (a::x) _).
    refine (ex_intro _ (x0) _).
    refine (ex_intro _ (x1) _).
    intuition.
    
    destruct H1. destruct H1. destruct H1. rewrite H1.
    refine (or_intror _).
    refine (ex_intro _ (a::x) _).
    refine (ex_intro _ (x0) _).
    refine (ex_intro _ (x1) _).
    intuition.
Qed.

Lemma cons_node_list : forall (x : PropF) xs, node_split (x::xs) =
  ((node_split (x::nil)) ++_ (node_split xs)).
Proof.
  intros. case x; intros; repeat (unfold tuple_app; simpl); trivial.
  case p0; intros; simpl; trivial.
Qed.

Lemma app_cons_nil : forall (x : PropF) A B,
  A ++ x :: B = (A ++ x :: nil) ++ B.
Proof.
  intros. rewrite <- app_assoc. rewrite <- app_comm_cons.
  simpl. trivial.
Qed.

Lemma node_split_single : forall x,
  (node_split (x::nil) = (x::nil, nil)) \/
  (exists y, (x = ¬y) /\ node_split (x::nil) = (nil, y::nil)).
Proof.
  intros; case x; intros;
    simpl; unfold tuple_app; simpl; intuition. case p0; intros; intuition.
    refine (or_intror _); refine (ex_intro _ p _); intuition.
Qed.

Theorem tableau_to_sequent : forall L,
  ClosedT_P L -> DerSeq_P (tuple_to_seq (node_split L)).
Proof.
  intros; induction H.
    assert (N := discriminate_neg); pose (N' := N A);
    pose (L' := in_split2 L N' H H0);
    destruct L'; destruct H1; destruct H1; destruct H1; rewrite H1;
    repeat (rewrite (tuple_list_app _);
    rewrite (cons_node_list _)).
      rewrite (cons_node_list (¬A)).
      pose proof (node_split_split x); destruct H2; destruct H2.
      pose proof (node_split_split x0); destruct H3; destruct H3.
      pose proof (node_split_split x1); destruct H4; destruct H4.
      rewrite H2; rewrite H3; rewrite H4; simpl. case A;
        unfold tuple_app; unfold tuple_to_seq; simpl; intros.
          apply (SId (# p)); intuition.
          apply (SId (⊥)); intuition.
          apply (SId (p ∧ p0)); intuition.
          apply (SId (p ∨ p0)); intuition.
          case p0; intros; simpl.
            apply (SId (p → # p1)); intuition.
            rewrite app_comm_cons; rewrite (app_assoc x3); apply (SImpR _);
              apply (SId p); intuition.
            apply (SId (p → p1 ∧ p2)); intuition.
            apply (SId (p → p1 ∨ p2)); intuition.
            apply (SId (p → p1 → p2)); intuition.
      
      rewrite (cons_node_list (A)).
      pose proof (node_split_split x); destruct H2; destruct H2.
      pose proof (node_split_split x0); destruct H3; destruct H3.
      pose proof (node_split_split x1); destruct H4; destruct H4.
      rewrite H2; rewrite H3; rewrite H4; simpl. case A;
        unfold tuple_app; unfold tuple_to_seq; simpl; intros.
          apply (SId (# p)); intuition.
          apply (SId (⊥)); intuition.
          apply (SId (p ∧ p0)); intuition.
          apply (SId (p ∨ p0)); intuition.
          case p0; intros; simpl.
            apply (SId (p → # p1)); intuition.
            apply (SImpR _);
              apply (SId p); simpl; intuition; apply (in_app_iff _);
              refine (or_intror _); apply (in_app_iff (⊥ :: x5)); 
              refine (or_intror _); intuition.
            apply (SId (p → p1 ∧ p2)); intuition.
            apply (SId (p → p1 ∨ p2)); intuition.
            apply (SId (p → p1 → p2)); intuition.
    
    pose (L' := in_split ⊥ L H); destruct L'; destruct H0.
    rewrite H0.
    repeat (rewrite (tuple_list_app _);
    rewrite (cons_node_list _)). simpl.
    pose proof (node_split_split x); destruct H1; destruct H1.
    pose proof (node_split_split x0); destruct H2; destruct H2.
    rewrite H1 in *; rewrite H2 in *; unfold tuple_app, tuple_to_seq; simpl.
    constructor; intuition.
    
    rewrite tuple_list_app in *;
    rewrite (cons_node_list) in *.
    rewrite (cons_node_list B) in IHClosedT_P.
    pose proof (node_split_split L1); destruct H0; destruct H0.
    pose proof (node_split_split L2); destruct H1; destruct H1.
    rewrite H0, H1 in *. simpl.
    unfold tuple_app, tuple_to_seq; simpl;
    destruct (node_split_single A), (node_split_single B).
      rewrite H2, H3 in *; unfold tuple_app, tuple_to_seq in *; simpl in *.
      clear H2. clear H3.
      apply SAndL; assumption.
      destruct H3; destruct H3; rewrite H2, H3, H4 in *.
      unfold tuple_app, tuple_to_seq in *; simpl in *. clear H2.
      apply SAndL. unfold Neg. rewrite (app_cons_nil A).
      apply (SImpL _).
        constructor; rewrite in_app_iff; refine (or_intror _); intuition.
        rewrite <- app_assoc. intuition.
      destruct H2; destruct H2; rewrite H2, H3, H4 in *.
      unfold tuple_app, tuple_to_seq in *; simpl in *. clear H3.
      apply SAndL. unfold Neg. apply (SImpL _).
        constructor; rewrite in_app_iff; refine (or_intror _); intuition.
        intuition.
      destruct H2, H3; destruct H2, H3; rewrite H2, H3, H4, H5 in *.
      unfold tuple_app, tuple_to_seq in *; simpl in *.
      apply SAndL; unfold Neg. rewrite (app_cons_nil (x3 → ⊥));
      apply (SImpL _).
      rewrite (app_cons_nil ⊥).
        constructor; intuition. rewrite <- (app_cons_nil (x3 → ⊥)).
        apply (SImpL _).
        constructor; intuition. assumption.
    
    rewrite tuple_list_app in *;
    rewrite (cons_node_list) in *.
    pose proof (node_split_split L1); destruct H1; destruct H1.
    pose proof (node_split_split L2); destruct H2; destruct H2.
    simpl in IHClosedT_P1; simpl in IHClosedT_P2.
    rewrite H1, H2 in *;
    unfold tuple_app, tuple_to_seq in *; simpl in *.
    apply (SAndR _ _ _ _); assumption.
    
    rewrite tuple_list_app in *;
    rewrite (cons_node_list) in *.
    pose proof (node_split_split L1); destruct H1; destruct H1.
    pose proof (node_split_split L2); destruct H2; destruct H2.
    destruct (node_split_single A), (node_split_single B).
    rewrite H1, H2, H3, H4 in *;
    unfold tuple_app, tuple_to_seq in *; simpl in *.
    clear H3. clear H4.
    apply SOrL; assumption.
    destruct H4; destruct H4.
    rewrite H1, H2, H3, H4, H5 in *;
    unfold tuple_app, tuple_to_seq in *; simpl in *. clear H3.
    apply SOrL. assumption.
    unfold Neg. apply SImpL.
    constructor; intuition. assumption.
    destruct H3; destruct H3.
    rewrite H1, H2, H3, H4, H5 in *;
    unfold tuple_app, tuple_to_seq in *; simpl in *. clear H4.
    apply SOrL.
    unfold Neg. apply SImpL.
    constructor; intuition. assumption.
    assumption.
    destruct H3; destruct H3; destruct H4; destruct H4.
    rewrite H1, H2, H3, H4, H5, H6 in *;
    unfold tuple_app, tuple_to_seq in *; simpl in *. clear H3. clear H4.
    apply SOrL.
    unfold Neg. apply SImpL.
    constructor; intuition. assumption.
    unfold Neg. apply SImpL.
    constructor; intuition. assumption.
    
    rewrite tuple_list_app in *;
    rewrite (cons_node_list) in *.
    pose proof (node_split_split L1); destruct H1; destruct H1.
    pose proof (node_split_split L2); destruct H2; destruct H2.
    destruct (node_split_single B).
    rewrite H1, H2, H3 in *.
    unfold tuple_app, tuple_to_seq in *; simpl in *. clear H3.
    case B in *; intros; simpl in *; try apply SImpL; assumption.
    destruct H3; destruct H3.
    rewrite H1, H2, H3, H4 in *.
    unfold tuple_app, tuple_to_seq in *; simpl in *.
    apply SImpL. unfold Neg; apply SImpL.
    constructor; intuition. assumption. assumption.
    
    rewrite tuple_list_app in *;
    rewrite (cons_node_list) in *;
    rewrite (cons_node_list (¬B)) in *.
    pose proof (node_split_split L1); destruct H0; destruct H0.
    pose proof (node_split_split L2); destruct H1; destruct H1.
    rewrite H0, H1 in *;
    unfold tuple_app, tuple_to_seq in *; simpl in *.
    apply SOrR; assumption.
    
    rewrite tuple_list_app in *;
    rewrite (cons_node_list) in *;
    rewrite (cons_node_list (¬B)) in *.
    pose proof (node_split_split L1); destruct H0; destruct H0.
    pose proof (node_split_split L2); destruct H1; destruct H1.
    destruct (node_split_single A).
    rewrite H0, H1, H2 in *.
    unfold tuple_app, tuple_to_seq in *; simpl in *. clear H2.
    apply SImpR. assumption.
    destruct H2; destruct H2.
    rewrite H0, H1, H2, H3 in *.
    unfold tuple_app, tuple_to_seq in *; simpl in *.
    apply SImpR. unfold Neg. apply SImpL.
    constructor; intuition. assumption.
Qed.

Lemma set_negate_distr : forall A B,
  SetNegate (A ++ B) = SetNegate A ++ SetNegate B.
Proof.
  intros; unfold SetNegate. apply map_app.
Qed.

Require Import Coq.Program.Equality.

Lemma tableau_comm : forall A B C D,
  ClosedT_P (A ++ (B ++ C) ++ D) <-> ClosedT_P (A ++ (C ++ B) ++ D).
Proof.
  intros; unfold iff; split; intros. dependent induction H. (* inversion H. *)
    apply (TId _ A0).
    repeat rewrite in_app_iff in *. rewrite (or_comm (In A0 C)).
    assumption.
    repeat rewrite in_app_iff in *. rewrite (or_comm (In (¬A0) C)).
    assumption.
      
    constructor. repeat rewrite in_app_iff in *.
    rewrite (or_comm (In ⊥ C)). assumption.
    pose (IH := IHClosedT_P A B C D).
    rewrite <- x in IH. intuition.
    
    assert (In (A0∧B0) (A ++ (B ++ C) ++ D)). rewrite <- H0; intuition.
    assert (In (A0∧B0) (A ++ (C ++ B) ++ D)).
    repeat rewrite in_app_iff in *; intuition.
    destruct (in_split _ _ H3). destruct H4. rewrite H4.
    apply TAnd.
Admitted.

Theorem sequent_to_tableau_P : forall Γ Δ,
  (DerSeq_P (Γ ⇒ Δ))
  -> ClosedT_P (Γ ++ SetNegate Δ).
Proof.
  intros. dependent induction H.
    apply in_split in H; destruct H; destruct H; rewrite H in *.
    apply in_split in H0; destruct H0; destruct H0; rewrite H0 in *.
    rewrite (set_negate_distr _); simpl.
    apply (TId _ A); intuition.
    
    apply in_split in H; destruct H; destruct H; rewrite H in *.
    constructor; intuition.
    
    pose (IH := IHDerSeq_P (Γ1 ++ A :: B :: Γ2) Δ). intuition.
    rewrite <- (app_assoc _). rewrite <- app_comm_cons.
    apply TAnd. rewrite <- app_assoc in H0; simpl in H0; assumption.
    
    pose (IH1 := IHDerSeq_P1 Γ (Δ1++A::Δ2)).
    pose (IH2 := IHDerSeq_P2 Γ (Δ1++B::Δ2)). intuition.
    clear IHDerSeq_P1. clear IHDerSeq_P2.
    rewrite set_negate_distr in *; simpl in *.
    rewrite app_assoc in *.
    exact (TNAnd _ _ _ _ H1 H2).
    
    pose (IH1 := IHDerSeq_P1 (Γ1++A::Γ2) Δ).
    pose (IH2 := IHDerSeq_P2 (Γ1++B::Γ2) Δ). intuition.
    clear IHDerSeq_P1. clear IHDerSeq_P2.
    rewrite <- app_assoc in *.
    rewrite <- app_comm_cons in *.
    exact (TOr _ _ _ _ H1 H2).
    
    pose (IH := IHDerSeq_P Γ (Δ1++A::B::Δ2)). intuition.
    clear IHDerSeq_P. rewrite set_negate_distr in *; simpl in *.
    rewrite app_assoc in *.
    exact (TNOr _ _ _ _ H0).
    
    pose (IH1 := IHDerSeq_P1 (Γ1++B::Γ2) (Δ1++Δ2)).
    pose (IH2 := IHDerSeq_P2 (Γ1++Γ2) (Δ1++A::Δ2)). intuition.
    clear IHDerSeq_P1. clear IHDerSeq_P2.
    rewrite set_negate_distr in *; simpl in *.
    rewrite <- app_assoc in *.
    rewrite <- app_comm_cons in *.
    rewrite (app_assoc Γ2) in H2.
    rewrite (app_cons_nil _) in H2.
    rewrite (tableau_comm _) in H2.
    simpl in H2.
    rewrite <- app_assoc in *.
    exact (TImp _ _ _ _ H2 H1).
    
    pose (IH := IHDerSeq_P (Γ1++A::Γ2) (Δ1++B::Δ2)). intuition.
    clear IHDerSeq_P.
    rewrite set_negate_distr in *; simpl in *.
    rewrite (app_cons_nil _) in H0.
    rewrite <- app_assoc in *.
    rewrite <- app_assoc in *.
    rewrite (app_assoc (A::nil)) in H0.
    rewrite (app_assoc (A::nil++Γ2)) in H0.
    rewrite <- (app_assoc (A::nil) Γ2) in H0.
    rewrite (tableau_comm _) in H0.
    repeat rewrite <- app_assoc in H0.
    rewrite <- (app_comm_cons _) in H0. simpl in H0.
    rewrite (app_assoc _) in H0. rewrite (app_assoc _) in H0.
    rewrite (app_assoc _). rewrite (app_assoc _).
    exact (TNImp _ _ _ _ H0).
Qed.

End equivalence_mod.