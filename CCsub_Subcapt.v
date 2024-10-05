Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Export CCsub_Lemmas.

(* Needed *)
Lemma subcapt_weakening : forall Γ Θ Δ C D,
  (Δ ++ Γ) ⊢ₛ C <: D ->
  (Δ ++ Θ ++ Γ) ⊢ wf ->
  (Δ ++ Θ ++ Γ) ⊢ₛ C <: D.
Proof with eauto using wf_cset_weakening.
  intros * Hsc Hwf.
  remember (Δ ++ Γ).
  remember (Δ ++ Θ ++ Γ).
  induction Hsc; subst...
Qed.

Lemma wf_cse_top: forall Γ,
  Γ ⊢ₛ cse_top wf.
Proof with eauto.
  intros *.
  constructor...
Qed.

Lemma wf_cse_bot: forall Γ,
  Γ ⊢ₛ cse_bot wf.
Proof with eauto.
  intros *.
  constructor...
Qed.



Hint Resolve wf_cse_top : core.
Hint Resolve wf_cse_bot : core.

(* Needed *)
Lemma subcapt_reflexivity : forall Γ C,
  Γ ⊢ wf ->
  Γ ⊢ₛ C wf ->
  Γ ⊢ₛ C <: C.
Proof with eauto.
  intros * WfE WfC.
  induction WfC. 
  - constructors... 
  - constructors... 
  - apply subcset_join_elim. auto. auto.
  - auto. 
Qed.

Lemma subcset_join_split : forall E R1 R2 T,
  E ⊢ₛ (cse_join R1 R2) <: T ->
  E ⊢ₛ R1 <: T /\ E ⊢ₛ R2 <: T.
Proof with eauto.
  intros * Sub.
  dependent induction Sub; try solve [intuition eauto]...
  - apply wf_cset_over_join in H0. destruct H0. split; constructor...
  - edestruct IHSub...
  - edestruct IHSub...
Qed.

(* Needed *)
Lemma subcapt_transitivity : forall E S Q T,
  E ⊢ₛ S <: Q ->
  E ⊢ₛ Q <: T ->
  E ⊢ₛ S <: T.
Proof with eauto with fsetdec.
  intros E S Q T SsubQ QsubT.
  generalize dependent T.
  induction SsubQ.
  - intros T QsubT... dependent induction QsubT...
  - intros T QsubT...
  - intros T QsubT...
  - intros T' QsubT...
  - intros T QsubT... eapply subcset_join_split in QsubT as [SubL SubR]...
  - intros T QsubT... eapply subcset_join_split in QsubT as [SubL SubR]...
  - intros T QsubT...
Qed.


(* Needed, line 664 *)
(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall x D Q C Δ Γ C1 C2 ,
  (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ₛ C1 <: C2 ->
  (* (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ wf -> *)
  Γ ⊢ₛ C <: D ->
  (map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cse x C C1) <: (subst_cse x C C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec.
  eauto 4 using wf_env_subst_cb, wf_cset_subst_cb, wf_cset_weaken_head.
  intros x D T C Δ Γ C1 C2 C1subC2 CsubD.
  remember (Δ ++ [(x, bind_typ (D # T))] ++ Γ).
  generalize dependent Δ.
  induction C1subC2; intros G ET; subst; simpl subst_cse; eauto.
  - apply subcapt_regular' in CsubD; destruct CsubD. destruct H2.
    eapply subcset_top. eapply wf_env_subst_cb...
    eapply wf_cset_subst_cb. apply H0. apply H. auto.
  - apply subcapt_regular' in CsubD; destruct CsubD. destruct H2.
    eapply subcset_bot. eapply wf_env_subst_cb... auto. eapply wf_cset_subst_cb.
    apply H0. assumption. assumption.
  - apply subcapt_regular' in CsubD; destruct CsubD. destruct H2.
    destruct (x == X).
    + apply subcapt_reflexivity... apply wf_cset_weaken_head...
    + apply subcapt_reflexivity... inversion H0. subst.
      binds_cases H6.
      * eauto.
      * econstructor.
        assert (binds X (bind_typ T0) (G ++ Γ)). {
          apply binds_head...
        }
        assert (binds X (subst_cb x C (bind_typ T0)) (map (subst_cb x C) G ++ Γ)).
        { apply (binds_map binding binding X (bind_typ T0) (subst_cb x C) (G ++ Γ)) in H4.
          auto. }
        apply H6.
  - destruct (x == X).
    + subst. 
      eapply (subcapt_transitivity (map (subst_cb X C) G ++ Γ) C D (subst_cse X C Q)).
      * rewrite_env (nil ++ (map (subst_cb X C) G ++ Γ)).
        apply subcapt_weakening...
        eapply wf_env_subst_cb. apply subcapt_regular' in C1subC2.
        destruct C1subC2. apply H0. apply subcapt_regular' in CsubD.
        destruct CsubD as [H0 [H1 H2]]...
      * rewrite (subst_cse_fresh X D C).
        -- binds_cases H.
        ++ simpl in Fr0. fsetdec. (* X in Γ *)
        ++ inversion H0. subst. apply IHC1subC2... (* X in [(X, bind_typ (D # T))] *)
        ++ (* X in G, contradiciton, environment is not ok *)
           assert (wf_env (G ++ [(X, bind_typ (D # T))] ++ Γ)) as Hwf.
           { apply subcapt_regular' in C1subC2. destruct C1subC2 as [hwf _]... }
           apply ok_from_wf_env in Hwf.
           apply fresh_mid_head in Hwf.
           apply binds_In in H1.
           unfold not in Hwf. apply Hwf in H1. inversion H1.
        -- apply (notin_fv_wf_cse Γ).
          ++ apply subcapt_regular' in CsubD. destruct CsubD as [_ [_ Dwf]]...
          ++ assert (wf_env (G ++ [(X, bind_typ (D # T))] ++ Γ)).
             { apply subcapt_regular' in C1subC2. destruct C1subC2 as [hwf _]... }
             apply ok_from_wf_env in H0.
             apply fresh_mid_tail in H0. assumption.
    + binds_cases H.
      * apply (subcset_trans_var (subst_cse x C R) (map (subst_cb x C) G ++ Γ) (subst_cse x C Q) X (subst_ct x C T0)).
        -- apply binds_tail.
          ++ rewrite (map_subst_cb_id Γ x C).
             apply binds_map with (f:=(subst_cb x C)) in H. simpl in H...
             apply subcapt_regular' in CsubD. destruct CsubD...
             apply subcapt_regular' in C1subC2. destruct C1subC2 as [Hwf _].
             apply ok_from_wf_env in Hwf. apply fresh_mid_tail in Hwf... 
          ++ rewrite dom_map...
        -- apply IHC1subC2... 
      * assert ((map (subst_cb x C) G ++ Γ) ⊢ₛ cse_fvar X <: subst_cse x C R).
        { apply (subcset_trans_var (subst_cse x C R) (map (subst_cb x C) G ++ Γ) (subst_cse x C R) X (subst_ct x C T0)).
          - assert (HH := H1).  
            apply binds_map with (f:=(subst_cb x C)) in H1. simpl in H1.
            apply subcapt_regular' in C1subC2. destruct C1subC2 as [Hwf _].
            apply ok_from_wf_env in Hwf. apply ok_remove_mid in Hwf.
            apply binds_head with (E:=Γ) in H1...
          - assert (HH := IHC1subC2 G).
            apply subcapt_regular' in HH. destruct HH as [HH1 [HH2 HH3]].
            apply subcapt_reflexivity.
            auto. auto. auto. 
        }
        eapply subcapt_transitivity. apply H. apply IHC1subC2...
  - constructor...
    eapply wf_cset_subst_cb. apply H.
    apply subcapt_regular' in C1subC2.
    destruct C1subC2 as [wf1 [wf2 wf3]]...
    apply subcapt_regular' in CsubD.
    destruct CsubD as [wf1 [wf2 wf3]]...
  - apply subcset_join_inr...
    eapply wf_cset_subst_cb. apply H.
    apply subcapt_regular' in C1subC2.
    destruct C1subC2 as [wf1 [wf2 wf3]]...
    apply subcapt_regular' in CsubD.
    destruct CsubD as [wf1 [wf2 wf3]]...
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
  (* (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ wf -> *)
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ C <: D ->
  Γ ⊢ P <: Q ->
  (map (subst_tb X P) Δ ++ Γ) ⊢ₛ C <: D.
Proof with simpl_env.
  eauto 4 using wf_env_subst_tb, wf_cset_subst_tb, wf_typ_subst_tb, wf_cset_weaken_head, sub_regular, subcapt_reflexivity with fsetdec.
  intros E P Q F Z S T SsubT PsubQ.
  assert (Envwf: wf_env (F ++ [(Z, bind_sub Q)] ++ E)).
  { apply subcapt_regular' in SsubT. destruct SsubT as [ewf _]. auto. }
  assert (PureQ : pure_type Q).
  { apply wf_env_tail in Envwf.
    inversion Envwf. auto. }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ PsubQ) PureQ)).
  remember (F ++ [(Z, bind_sub Q)] ++ E) as G in |-.
  rewrite <- HeqG in SsubT. rewrite <- HeqG in Envwf.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl...
  - apply subcset_top; 
    (try eapply wf_cset_subst_tb; try eapply wf_env_subst_tb; 
    try apply H0; try apply Envwf; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 subwf3]]; auto; auto).
  - apply subcset_bot; 
    (try eapply wf_cset_subst_tb; try eapply wf_env_subst_tb; 
    try apply H0; try apply Envwf; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 subwf3]]; auto; auto).
  - apply subcset_refl_var;
    (try eapply wf_cset_subst_tb; try eapply wf_env_subst_tb; 
    try apply H0; try apply Envwf; apply sub_regular in PsubQ;
    destruct PsubQ as [subwf1 [subwf2 subwf3]]; auto; auto).
  - apply (subcset_trans_var R (map (subst_tb Z P) G ++ E) Q0 X (subst_tt Z P T))...
    binds_cases H. 
    + (* X in E *)
      apply binds_tail. eapply binds_map with (f := subst_tb Z P) in H. simpl in H.
      erewrite <- map_subst_tb_id in H. apply H. eauto.
      apply binding_uniq_from_wf_env in Envwf. auto.
      apply binding_uniq_from_wf_env in Envwf. auto.
    + (* X in G *)
      apply binds_head.
      eapply binds_map with (f := subst_tb Z P) in H1. simpl in H1.
      apply H1.
    + auto.
  - apply subcset_join_inl; auto.
    eapply wf_cset_subst_tb.
    apply H. apply sub_regular in PsubQ as [_ [Pwf _]]. auto.
    auto.
  - apply subcset_join_inr; auto.
    eapply wf_cset_subst_tb.
    apply H. apply sub_regular in PsubQ as [_ [Pwf _]]. auto.
    auto.
  - apply subcset_join_elim; auto.
Qed.

