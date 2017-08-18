Require Export b_sequent_calculus Omega Coq.Program.Equality Coq.Program.Tactics.
Set Implicit Arguments.

Module Type admissibility_mod
  (X : base_mod) (Y : sequent_calculus_mod X).
Import X Y.

Lemma eqlist_permute1 :
  forall (x y a b : list PropF) (A D E : PropF), x++A::y = a++D::E::b ->
    ((exists x1 x2, x = x1++x2::nil /\ (a=x1 /\ D=x2 /\ E=A /\ b=y)) \/
     (exists y1 y2, y = y1::y2 /\ (a=x /\ D=A /\ E=y1 /\ b=y2)) \/
     (exists y1 y2 y3 y4, y=y1++y2::y3::y4 /\ a=x++A::y1 /\ D=y2 /\ E=y3 /\ b=y4) \/
     (exists x1 x2 x3 x4, x=x1++x2::x3::x4 /\ a=x1 /\ D=x2 /\ E=x3 /\ b=x4++A::y)).
Proof.
  intros. assert (In A (a ++ D :: E :: b)). rewrite <- H; intuition.
  rewrite in_app_iff in H0; simpl in H0. repeat destruct H0.
    refine (or_intror _); refine (or_intror _); refine (or_introl _).
    case y.
Admitted.

Ltac seq_apply := (apply (SAndL _) || apply (SAndR _) ||
                   apply (SOrL _)  || apply (SOrR _)  ||
                   apply (SImpL _) || apply (SImpR _)).

Theorem interchange_L_help :
  forall Γ1 Γ2 Δ n, (forall D E, n = (grade D) + (grade E) -> 
    DerSeq (Γ1++D++E++Γ2 ⇒ Δ) -> DerSeq (Γ1++E++D++Γ2 ⇒ Δ)).
Proof.
  intros. induction n. intros; induction D, E;
  try (unfold grade in *; simpl in H; discriminate H); simpl in *; intuition.
  case p, a; simpl in *; intuition. admit.
  constructor; repeat (rewrite in_app_iff; simpl; intuition).
  constructor; repeat (rewrite in_app_iff; simpl; intuition).
  constructor; repeat (rewrite in_app_iff; simpl; intuition).
  
  dependent induction H0.
    (* Id *)
    apply (SId A).
    repeat rewrite in_app_iff in *; simpl in *; intuition.
    assumption.

    (* Bot *)
    apply SBot.
    repeat rewrite in_app_iff in *; simpl in *; intuition.

(*
    (* AndL *)
    pose proof (eqlist_permute1 Γ0 Γ3 Γ1 Γ2 (A∧B) D E); intuition.
      destruct_exists. destruct_conjs.
    pose (IH' := IHDerSeq p0 p); intuition; pose (IH := IH' p0 p)
    pose (IH := IHDerSeq Γ0 Γ3 Δ A B). intuition. apply SAndL in H0.
*)
Admitted.

Theorem interchange_L :
  forall Γ1 Γ2 Δ D E,
    DerSeq (Γ1++D::E::Γ2 ⇒ Δ) -> DerSeq (Γ1++E::D::Γ2 ⇒ Δ).
Admitted.

Theorem interchange_R :
  forall Γ Δ1 Δ2 D E,
    DerSeq (Γ ⇒ Δ1++D::E::Δ2) -> DerSeq (Γ ⇒ Δ1++E::D::Δ2).
Admitted.

Theorem thinning_L :
  forall Γ Δ D, DerSeq (Γ ⇒ Δ) -> DerSeq (D::Γ ⇒ Δ).
Proof.
  intros. dependent induction H.
    (* Id *)
    apply in_split in H; apply in_split in H0;
    destruct H; destruct H; destruct H0; destruct H0;
    rewrite H; rewrite H0.
    apply (SId A); intuition.

    (* Bot *)
    apply in_split in H; destruct H; destruct H; rewrite H.
    apply SBot; intuition.

    (* AndL *)
    pose (IH := IHDerSeq (Γ1++A::B::Γ2) Δ); intuition.
    rewrite app_comm_cons; apply SAndL; intuition.

    (* AndR *)
    pose (IH := IHDerSeq1 Γ (Δ1++A::Δ2)); intuition;
    pose (IH := IHDerSeq2 Γ (Δ1++B::Δ2)); intuition.
    apply SAndR; assumption.

    (* OrL *)
    pose (IH := IHDerSeq1 (Γ1++A::Γ2) Δ); intuition;
    pose (IH := IHDerSeq2 (Γ1++B::Γ2) Δ); intuition.
    rewrite app_comm_cons; apply SOrL; assumption.

    (* OrR *)
    pose (IH := IHDerSeq Γ (Δ1++A::B::Δ2)); intuition.
    apply SOrR; assumption.

    (* ImpL *)
    pose (IH := IHDerSeq1 (Γ1++B::Γ2) Δ); intuition;
    pose (IH := IHDerSeq2 (Γ1++Γ2) (A::Δ)); intuition.
    rewrite app_comm_cons; apply SImpL; intuition.

    (* ImpR *)
    pose (IH := IHDerSeq (A::Γ) (Δ1++B::Δ2)); intuition.
    apply SImpR. apply (interchange_L nil Γ D A); intuition.
    (* Need Exchange Lemma *)
Qed.

Theorem thinning_R :
  forall Γ Δ D, DerSeq (Γ ⇒ Δ) -> DerSeq (Γ ⇒ D::Δ).
Proof.
  intros. dependent induction H.
    (* Id *)
    apply in_split in H; apply in_split in H0;
    destruct H; destruct H; destruct H0; destruct H0;
    rewrite H; rewrite H0.
    apply (SId A); intuition.

    (* Bot *)
    apply in_split in H; destruct H; destruct H; rewrite H.
    apply SBot; intuition.

    (* AndL *)
    pose (IH := IHDerSeq (Γ1++A::B::Γ2) Δ); intuition;
    apply SAndL; assumption.

    (* AndR *)
    pose (IH := IHDerSeq1 Γ (Δ1++A::Δ2)); intuition;
    pose (IH := IHDerSeq2 Γ (Δ1++B::Δ2)); intuition.
    rewrite app_comm_cons; apply SAndR; assumption.

    (* OrL *)
    pose (IH := IHDerSeq1 (Γ1++A::Γ2) Δ); intuition;
    pose (IH := IHDerSeq2 (Γ1++B::Γ2) Δ); intuition.
    apply SOrL; assumption.

    (* OrR *)
    pose (IH := IHDerSeq Γ (Δ1++A::B::Δ2)); intuition.
    rewrite app_comm_cons; apply SOrR; assumption.

    (* ImpL *)
    pose (IH := IHDerSeq1 (Γ1++B::Γ2) Δ); intuition;
    pose (IH := IHDerSeq2 (Γ1++Γ2) (A::Δ)); intuition.
    apply SImpL; intuition.
    apply (interchange_R nil Δ D A); intuition.

    (* ImpR *)
    pose (IH := IHDerSeq (A::Γ) (Δ1++B::Δ2)); intuition.
    rewrite app_comm_cons; apply SImpR; intuition.
    (* Need Exchange Lemma *)
Qed.



End admissibility_mod.