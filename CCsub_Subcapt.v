Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Export CCsub_Lemmas.

(* Needed *)
Lemma subcapt_weakening : forall Γ Θ Δ C D,
  subcapt (Δ ++ Γ) C D ->
  wf_ctx (Δ ++ Θ ++ Γ) ->
  subcapt (Δ ++ Θ ++ Γ) C D.
Proof with eauto using wf_cse_weakening.
  intros * Hsc Hwf.
  remember (Δ ++ Γ).
  remember (Δ ++ Θ ++ Γ).
  induction Hsc; subst...
Qed.

Lemma wf_cse_top: forall Γ,
  wf_cse Γ cse_top.
Proof with eauto.
  intros *.
  constructor...
Qed.

Lemma wf_cse_bot: forall Γ,
  wf_cse Γ cse_bot.
Proof with eauto.
  intros *.
  constructor...
Qed.

Hint Resolve wf_cse_top : core.
Hint Resolve wf_cse_bot : core.

(* Needed *)
Lemma subcapt_reflexivity : forall Γ C,
  wf_ctx Γ ->
  wf_cse Γ C ->
  subcapt Γ C C.
Proof with eauto.
  intros * WfE WfC.
  induction WfC; eauto.
  apply subcapt_join_elim. auto. auto.
Qed.

Lemma subcapt_join_split : forall E R1 R2 T,
  subcapt E (cse_join R1 R2) T ->
  subcapt E R1 T /\ subcapt E R2 T.
Proof with eauto.
  intros * Sub.
  dependent induction Sub; try solve [intuition eauto]...
  - split; constructor; inversion H0...
  - edestruct IHSub...
  - edestruct IHSub...
Qed.

Lemma subcapt_top_top : forall E C D,
  wf_cse E D ->
  subcapt E cse_top C ->
  subcapt E D C.
Proof with eauto.
  intros * WfD Sub.
  dependent induction Sub...
Qed.

(* Needed *)
Lemma subcapt_transitivity : forall E R Q T,
  subcapt E R Q ->
  subcapt E Q T ->
  subcapt E R T.
Proof with eauto with fsetdec.
  intros E R Q T RsubQ QsubT.
  generalize dependent T.
  induction RsubQ; intros T' QsubT...
  - apply subcapt_top_top with (D := Q) in QsubT...
  - eapply subcapt_join_split in QsubT as [SubL SubR]...
  - eapply subcapt_join_split in QsubT as [SubL SubR]...
Qed.

(* Needed, line 664 *)
(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cse : forall x D Q C Δ Γ C1 C2 ,
  subcapt (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) C1 C2 ->
  subcapt Γ C D ->
  subcapt (map (subst_cb x C) Δ ++ Γ) (subst_cse x C C1) (subst_cse x C C2).
Proof with eauto using wf_ctx_subst_cb, wf_cse_subst_cb with fsetdec.
  eauto 4 using wf_ctx_subst_cb, wf_cse_subst_cb, wf_cse_weaken_head.
  intros x D T C Δ Γ C1 C2 C1subC2 CsubD.
  remember (Δ ++ [(x, bind_typ (D # T))] ++ Γ).
  generalize dependent Δ.
  induction C1subC2; intros G ET; subst; simpl subst_cse; eauto.
  - apply subcapt_regular in CsubD; destruct CsubD as [WfCtx [WfC WfD]].
    eapply subcapt_top...
  - apply subcapt_regular in CsubD; destruct CsubD as [WfCtx [WfC WfD]].
    eapply subcapt_bot...
  - apply subcapt_regular in CsubD; destruct CsubD as [WfCtx [WfC WfD]].
    destruct (x == X).
    + apply subcapt_reflexivity... apply wf_cse_weaken_head...
    + apply subcapt_reflexivity... inversion H0. subst.
      binds_cases H3.
      * eauto.
      * econstructor.
        assert (binds X (bind_typ T0) (G ++ Γ)). {
          apply binds_head...
        }
        assert (binds X (subst_cb x C (bind_typ T0)) (map (subst_cb x C) G ++ Γ)).
        { apply (binds_map binding binding X (bind_typ T0) (subst_cb x C) (G ++ Γ)) in H1.
          auto. }
        apply H3.
  - assert (HCtx: wf_ctx (G ++ [(x, bind_typ (D # T))] ++ Γ)).
    { apply subcapt_regular in C1subC2. destruct C1subC2 as [hwf _]... }
    destruct (x == X).
    + subst.
      eapply (subcapt_transitivity (map (subst_cb X C) G ++ Γ) C D (subst_cse X C Q)).
      * rewrite_env (nil ++ (map (subst_cb X C) G ++ Γ)).
        apply subcapt_weakening...
        eapply wf_ctx_subst_cb. apply subcapt_regular in C1subC2.
        destruct C1subC2 as [WfCtx _]. apply WfCtx. apply subcapt_regular in CsubD.
        destruct CsubD as [_ [H3 _]]...
      * rewrite (subst_cse_fresh X D C).
        binds_cases H.
        ++ simpl in Fr0. fsetdec. (* X in Γ *)
        ++ inversion H0. subst. apply IHC1subC2... (* X in [(X, bind_typ (D # T))] *)
        ++ (* X in G, contradiciton, environment is not ok *)
           apply ok_from_wf_ctx in HCtx.
           apply fresh_mid_head in HCtx.
           apply binds_In in H1.
           unfold not in HCtx. apply HCtx in H1. inversion H1.
        ++ apply (notin_fv_wf_cse Γ).
           -- apply subcapt_regular in CsubD. destruct CsubD as [_ [_ Dwf]]...
           -- apply ok_from_wf_ctx in HCtx.
              apply fresh_mid_tail in HCtx. assumption.
    + binds_cases H.
      * apply (subcapt_trans_var (subst_cse x C R) (map (subst_cb x C) G ++ Γ) (subst_cse x C Q) X (subst_ct x C T0)).
        -- apply binds_tail.
          ++ rewrite (map_subst_cb_id Γ x C).
             apply binds_map with (f:=(subst_cb x C)) in H. simpl in H...
             apply subcapt_regular in CsubD. destruct CsubD...
             apply subcapt_regular in C1subC2.
             apply ok_from_wf_ctx in HCtx. apply fresh_mid_tail in HCtx...
          ++ rewrite dom_map...
        -- apply IHC1subC2... 
      * assert (subcapt (map (subst_cb x C) G ++ Γ) (cse_fvar X) (subst_cse x C R)).
        { apply (subcapt_trans_var (subst_cse x C R) (map (subst_cb x C) G ++ Γ) (subst_cse x C R) X (subst_ct x C T0)).
          - assert (HH := H1).
            apply binds_map with (f:=(subst_cb x C)) in H1. simpl in H1.
            apply subcapt_regular in C1subC2.
            apply ok_from_wf_ctx in HCtx. apply ok_remove_mid in HCtx.
            apply binds_head with (E:=Γ) in H1...
          - apply subcapt_reflexivity...
        }
        eapply subcapt_transitivity. apply H. apply IHC1subC2...
  - constructor...
  - apply subcapt_join_inr...
Qed.

Tactic Notation "subst_mem_singleton" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; subst
  end.

Tactic Notation "subst_mem_singleton" "<-" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; symmetry in H; subst
  end.

(* Needed *)
Lemma subcapt_through_subst_tt : forall Γ P Q Δ X C D,
  subcapt (Δ ++ [(X, bind_sub Q)] ++ Γ) C D ->
  sub Γ P Q ->
  subcapt (map (subst_tb X P) Δ ++ Γ) C D.
Proof with simpl_env; eauto.
  eauto 4 using wf_ctx_subst_tb, wf_cse_subst_tb, wf_typ_subst_tb, wf_cse_weaken_head, sub_regular, subcapt_reflexivity with fsetdec.
  intros E P Q F Z R T SsubT PsubQ.
  assert (WfCtx: wf_ctx (F ++ [(Z, bind_sub Q)] ++ E)).
  { apply subcapt_regular in SsubT. destruct SsubT as [ewf _]. auto. }
  assert (PureQ : pure_type Q).
  { apply wf_ctx_tail in WfCtx.
    inversion WfCtx. auto. }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ PsubQ) PureQ)).
  remember (F ++ [(Z, bind_sub Q)] ++ E) as G in |-.
  rewrite <- HeqG in SsubT. rewrite <- HeqG in WfCtx.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl...
  - apply subcapt_top;
    (try eapply wf_cse_subst_tb; try eapply wf_ctx_subst_tb;
    try apply H0; try apply WfCtx; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 subwf3]]; auto; auto).
  - apply subcapt_bot;
    (try eapply wf_cse_subst_tb; try eapply wf_ctx_subst_tb; 
    try apply H0; try apply WfCtx; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 subwf3]]; auto; auto).
  - apply subcapt_refl_var;
    (try eapply wf_cse_subst_tb; try eapply wf_ctx_subst_tb; 
    try apply H0; try apply WfCtx; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 subwf3]]; auto; auto).
  - apply (subcapt_trans_var R (map (subst_tb Z P) G ++ E) Q0 X (subst_tt Z P T))...
    binds_cases H. 
    + (* X in E *)
      apply binds_tail. eapply binds_map with (f := subst_tb Z P) in H. simpl in H.
      erewrite <- map_subst_tb_id in H. apply H. eauto.
      apply binding_uniq_from_wf_ctx in WfCtx. auto.
      apply binding_uniq_from_wf_ctx in WfCtx. auto.
    + (* X in G *)
      apply binds_head.
      eapply binds_map with (f := subst_tb Z P) in H1. simpl in H1.
      apply H1.
  - apply subcapt_join_inl; auto.
    eapply wf_cse_subst_tb.
    apply H. apply sub_regular in PsubQ as [_ [Pwf _]]...
  - apply subcapt_join_inr; auto.
    eapply wf_cse_subst_tb.
    apply H. apply sub_regular in PsubQ as [_ [Pwf _]]...
Qed.

