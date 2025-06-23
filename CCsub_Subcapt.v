Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Export CCsub_Lemmas.

(* Needed *)
Lemma subcapt_weakening : forall Γ Θ Δ C D S,
  subcapt (Δ ++ Γ) S C D ->
  wf_ctx (Δ ++ Θ ++ Γ) S ->
  subcapt (Δ ++ Θ ++ Γ) S C D.
Proof with eauto using wf_cse_weakening.
  intros * Hsc Hwf.
  remember (Δ ++ Γ).
  remember (Δ ++ Θ ++ Γ).
  induction Hsc; subst...
Qed.

Lemma subcapt_weakening_store : forall Γ S1 S2 S3 C D,
  subcapt Γ (S1 ++ S3) C D ->
  wf_store_ctx (S1 ++ S2 ++ S3) ->
  subcapt Γ (S1 ++ S2 ++ S3) C D.
Proof with eauto using
  wf_cse_weakening_store,
  wf_typ_weakening_store,
  wf_ctx_weakening_store.
  intros * Hsc Hwf.
  dependent induction Hsc; subst...
Qed.

Lemma wf_cse_top: forall Γ S,
  wf_cse Γ S cse_top.
Proof with eauto.
  intros *.
  constructor...
Qed.

Lemma wf_cse_bot: forall Γ S,
  wf_cse Γ S cse_bot.
Proof with eauto.
  intros *.
  constructor...
Qed.

Hint Resolve wf_cse_top : core.
Hint Resolve wf_cse_bot : core.

(* Needed *)
Lemma subcapt_reflexivity : forall Γ S C,
  wf_ctx Γ S ->
  wf_cse Γ S C ->
  subcapt Γ S C C.
Proof with eauto.
  intros * WfE WfC.
  induction WfC; eauto.
  apply subcapt_join_elim. auto. auto.
Qed.

Lemma subcapt_join_split : forall E S R1 R2 T,
  subcapt E S (cse_join R1 R2) T ->
  subcapt E S R1 T /\ subcapt E S R2 T.
Proof with eauto.
  intros * Sub.
  dependent induction Sub; try solve [intuition eauto]...
  - split; constructor; inversion H0...
  - edestruct IHSub...
  - edestruct IHSub...
Qed.

Lemma subcapt_top_top : forall E S C D,
  wf_cse E S D ->
  subcapt E S cse_top C ->
  subcapt E S D C.
Proof with eauto.
  intros * WfD Sub.
  assert (wf_store_ctx S) by (apply subcapt_regular in Sub; destruct Sub; auto).
  dependent induction Sub...
Qed.

(* Needed *)
Lemma subcapt_transitivity : forall E S R Q T,
  subcapt E S R Q ->
  subcapt E S Q T ->
  subcapt E S R T.
Proof with eauto with fsetdec.
  intros E S R Q T RsubQ QsubT.
  generalize dependent T.
  induction RsubQ; intros T' QsubT...
  - apply subcapt_top_top with (D := Q) in QsubT...
  - eapply subcapt_join_split in QsubT as [SubL SubR]...
  - eapply subcapt_join_split in QsubT as [SubL SubR]...
Qed.

Lemma wf_store_cse_no_fvar: forall S x R T l,
  wf_store_ctx S ->
  StoreImpl.binds l (R # T) S ->
  x `notin`a `cse_fvars` R.
Admitted.
(* Proof with eauto.
  intros * WfS HBinds.
  induction WfS...
  - inversion HBinds.
  - Store.binds_cases HBinds.
    + apply (IHWfS H1).
    + inversion H3. subst.
      inversion H; subst.
      inversion H4; subst...
      -- inversion H1.
      -- apply wf_cse_fvars_from_ctx in H4.
         fsetdec.
Qed. *)

(* Needed, line 664 *)
(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cse : forall x D Q C Δ Γ S C1 C2 ,
  subcapt (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) S C1 C2 ->
  subcapt Γ S C D ->
  subcapt (EnvImpl.map (subst_cb x C) Δ ++ Γ) S (subst_cse x C C1) (subst_cse x C C2).
(* Proof with eauto using wf_ctx_subst_cb, wf_cse_subst_cb with fsetdec.
  eauto 4 using wf_ctx_subst_cb, wf_cse_subst_cb, wf_cse_weaken_head.
  intros x D T C Δ Γ S C1 C2 C1subC2 CsubD.
  remember (Δ ++ [(x, bind_typ (D # T))] ++ Γ).
  generalize dependent Δ.
  induction C1subC2; intros G ET; subst; simpl subst_cse; eauto.
  - apply subcapt_regular in CsubD; destruct CsubD as [WfS [WfCtx [WfC WfD]]].
    eapply subcapt_top...
  - apply subcapt_regular in CsubD; destruct CsubD as [WfS [WfCtx [WfC WfD]]].
    eapply subcapt_bot...
  - apply subcapt_regular in CsubD; destruct CsubD as [WfS [WfCtx [WfC WfD]]].
    destruct (x == X).
    + apply subcapt_reflexivity... apply wf_cse_weaken_head...
    + apply subcapt_reflexivity... inversion H0. subst.
      binds_cases H4.
      * admit.
      (* * econstructor.
        assert (binds X (bind_typ T0) (G ++ Γ)). {
          apply binds_head...
        }
        assert (binds X (subst_cb x C (bind_typ T0)) (EnvImpl.map (subst_cb x C) G ++ Γ)).
        { apply (binds_map binding binding X (bind_typ T0) (subst_cb x C) (G ++ Γ)) in H1.
          auto. }
        apply H3. *)
  - constructor...
    apply (wf_cse_subst_cb Γ G (D # T) x (cse_loc l) C S)...
  - destruct (x == X).
    + subst.
      eapply (subcapt_transitivity (EnvImpl.map (subst_cb X C) G ++ Γ) S C D (subst_cse X C Q)).
      * rewrite_env (nil ++ (EnvImpl.map (subst_cb X C) G ++ Γ)).
        apply subcapt_weakening...
        (* eapply wf_ctx_subst_cb. apply subcapt_regular in C1subC2.
        destruct C1subC2 as [WfS [WfCtx _]]. apply WfCtx. apply subcapt_regular in CsubD.
        destruct CsubD as [_ [_ [H3 _]]]... *)
      * rewrite (subst_cse_fresh X D C).
        -- binds_cases H.
        ++ admit.
            (* simpl in Fr0. fsetdec. X in Γ *)
        (* ++ inversion H0. subst. apply IHC1subC2... (* X in [(X, bind_typ (D # T))] *)
        ++ (* X in G, contradiciton, environment is not ok *)
           assert (wf_ctx (G ++ [(X, bind_typ (D # T))] ++ Γ) S) as HCtx.
           { apply subcapt_regular in C1subC2. destruct C1subC2 as [_ [hwf _]]... }
           apply ok_from_wf_ctx in HCtx.
           apply fresh_mid_head in HCtx.
           apply binds_In in H1.
           unfold not in HCtx. apply HCtx in H1. inversion H1. *)
        -- apply (notin_fv_wf_cse Γ) with (S := S).
          ++ apply subcapt_regular in CsubD. destruct CsubD as [_ [_ [_ Dwf]]]...
          ++ admit.
             (* assert (wf_ctx (G ++ [(X, bind_typ (D # T))] ++ Γ) S).
             { apply subcapt_regular in C1subC2. destruct C1subC2 as [_ [hwf _]]... }
             apply ok_from_wf_ctx in H0.
             apply fresh_mid_tail in H0. assumption. *)
    + binds_cases H.
      * apply (subcapt_trans_var (subst_cse x C R) S (EnvImpl.map (subst_cb x C) G ++ Γ) (subst_cse x C Q) X (subst_ct x C T0)).
        -- apply EnvImpl.binds_app_3.
          ++ admit.
             (* rewrite (EnvImpl.map_subst_cb_id Γ x C S).
             apply binds_map with (f:=(subst_cb x C)) in H. simpl in H...
             apply subcapt_regular in CsubD. destruct CsubD...
             apply subcapt_regular in C1subC2. destruct C1subC2 as [_ [HCtx _]].
             apply ok_from_wf_ctx in HCtx. apply fresh_mid_tail in HCtx...  *)
          (* ++ rewrite dom_map... *)
        -- apply IHC1subC2... 
      (* * assert (subcapt (EnvImpl.map (subst_cb x C) G ++ Γ) S (cse_fvar X) (subst_cse x C R)).
        { apply (subcapt_trans_var (subst_cse x C R) S (EnvImpl.map (subst_cb x C) G ++ Γ) (subst_cse x C R) X (subst_ct x C T0)).
          - assert (HH := H1).
            apply binds_map with (f:=(subst_cb x C)) in H1. simpl in H1.
            apply subcapt_regular in C1subC2. destruct C1subC2 as [_ [HCtx _]].
            apply ok_from_wf_ctx in HCtx. apply ok_remove_mid in HCtx.
            apply binds_head with (E:=Γ) in H1...
          - assert (HH := IHC1subC2 CsubD G ltac:(fsetdec)).
            apply subcapt_regular in HH. destruct HH as [HH1 [HH2 [HH3 HH4]]].
            apply subcapt_reflexivity.
            auto. auto.
        }
        eapply subcapt_transitivity. apply H. apply IHC1subC2... *)
  - admit.
    (* specialize (IHC1subC2 CsubD G ltac:(fsetdec)).
    epose proof (subcapt_regular _ _ _ _ CsubD) as [WfS [WfCtx [WfC _]]].
    epose proof (subcapt_regular _ _ _ _ C1subC2) as [_ [WfCtx2 _]].
    epose proof (wf_store_cse_no_fvar _ x _ _ _ WfS H) as HR.
    assert (subcapt (EnvImpl.map (subst_cb x C) G ++ Γ) S (cse_loc X) (subst_cse x C R)). {
      apply subcapt_trans_loc with (R := R) (T := T0)...
      rewrite <- (subst_cse_fresh x R C)...
      apply subcapt_reflexivity...
      epose proof (wf_pair_from_wf_store_ctx nil S R T0 X WfS ltac:(constructor) H) as [WfR _]...
      rewrite_env ((EnvImpl.map (subst_cb x C) G ++ Γ) ++ nil).
      apply wf_cse_weaken_head with (Δ := (EnvImpl.map (subst_cb x C) G ++ Γ))...
      simpl_env.
      apply ok_from_wf_ctx in WfCtx2.
      apply ok_remove_mid in WfCtx2.
      apply ok_map_app_l with (f := (subst_cb x C)) in WfCtx2...
    }
    eapply subcapt_transitivity with (Q := (subst_cse x C R)) ... *)
  - constructor...
  - apply subcapt_join_inr...
    Unshelve. all: eauto. *)
Admitted.

Tactic Notation "subst_mem_singleton" hyp(H) :=
  match type of H with
    | _ `in`a _ => rewrite AtomSetFacts.singleton_iff in H; subst
  end.

Tactic Notation "subst_mem_singleton" "<-" hyp(H) :=
  match type of H with
    | _ `in`a _ => rewrite AtomSetFacts.singleton_iff in H; symmetry in H; subst
  end.

(* Needed *)
Lemma subcapt_through_subst_tt : forall Γ P Q Δ X C D S,
  subcapt (Δ ++ [(X, bind_sub Q)] ++ Γ) S C D ->
  sub Γ S P Q ->
  subcapt (EnvImpl.map (subst_tb X P) Δ ++ Γ) S C D.
(* Proof with simpl_env; eauto.
  eauto 4 using wf_ctx_subst_tb, wf_cse_subst_tb, wf_typ_subst_tb, wf_cse_weaken_head, sub_regular, subcapt_reflexivity with fsetdec.
  intros E P Q F Z R T S SsubT PsubQ.
  assert (WfCtx: wf_ctx (F ++ [(Z, bind_sub Q)] ++ E) S).
  { apply subcapt_regular in SsubT. destruct SsubT as [_ [ewf _]]. auto. }
  assert (PureQ : pure_type Q).
  { apply wf_ctx_tail in WfCtx.
    inversion WfCtx. auto. }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ S PsubQ) PureQ)).
  remember (F ++ [(Z, bind_sub Q)] ++ E) as G in |-.
  rewrite <- HeqG in SsubT. rewrite <- HeqG in WfCtx.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl...
  - apply subcapt_top;
    (try eapply wf_cse_subst_tb; try eapply wf_ctx_subst_tb; 
    try apply H0; try apply WfCtx; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 [subwf3 subwf4]]]; auto; auto).
  - apply subcapt_bot;
    (try eapply wf_cse_subst_tb; try eapply wf_ctx_subst_tb; 
    try apply H0; try apply WfCtx; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 [subwf3 subwf4]]]; auto; auto).
  - apply subcapt_refl_var;
    (try eapply wf_cse_subst_tb; try eapply wf_ctx_subst_tb; 
    try apply H0; try apply WfCtx; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 [subwf3 subwf4]]]; auto; auto).
  - apply subcapt_refl_loc;
    (try eapply wf_cse_subst_tb; try eapply wf_ctx_subst_tb; 
    try apply H0; try apply WfCtx; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 [subwf3 subwf4]]]; auto; auto).
  - apply (subcapt_trans_var R S (EnvImpl.map (subst_tb Z P) G ++ E) Q0 X (subst_tt Z P T))...
    binds_cases H. 
    + admit. (* X in E *)
      (* apply EnvImpl.binds_app_3. eapply binds_map with (f := subst_tb Z P) in H. simpl in H.
      erewrite <- map_subst_tb_id in H. apply H. eauto.
      apply binding_uniq_from_wf_ctx in WfCtx. auto.
      apply binding_uniq_from_wf_ctx in WfCtx. auto. *)
    (* + X in G *)
      (* apply binds_head.
      eapply binds_map with (f := subst_tb Z P) in H1. simpl in H1.
      apply H1. *)
  - apply subcapt_join_inl; auto.
    eapply wf_cse_subst_tb.
    apply H. apply sub_regular in PsubQ as [_ [_ [Pwf _]]]...
  - apply subcapt_join_inr; auto.
    eapply wf_cse_subst_tb.
    apply H. apply sub_regular in PsubQ as [_ [_ [Pwf _]]]... *)
Admitted.

