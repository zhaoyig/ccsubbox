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
  - apply subcapt_universal; eapply wf_cset_weakening...
  - apply subcapt_in...
  - apply subcapt_set...
    intros X XNotIn...
Qed.

Lemma wf_cset_fvarless : forall Γ univ,
  Γ ⊢ₛ (cset_set {}A {}N univ) wf.
Proof with eauto.
  intros *.
  constructor...
  intros ? ?.
  exfalso; fsetdec.
Qed.

Hint Resolve wf_cset_fvarless : core.

(* Needed *)
Lemma subcapt_reflexivity : forall Γ C,
  Γ ⊢ₛ C wf ->
  Γ ⊢ₛ C <: C.
Proof with eauto.
  intros * WfC.
  inversion WfC; subst.
  constructor...
  - intros y yIn.
    apply subcapt_in...
    + apply (wf_cset_singleton_by_mem fvars univ)...
  - destruct univ...
Qed.

(* Needed *)
Lemma subcapt_transitivity : forall D Γ C E,
  Γ ⊢ wf ->
  Γ ⊢ₛ C <: D ->
  Γ ⊢ₛ D <: E ->
  Γ ⊢ₛ C <: E.
Proof with eauto with fsetdec.
  intros * WfE SCD SDE.
  note (Γ ⊢ₛ E wf).
  dependent induction SCD...
  - Case "subcapt_universal".
    inversion SDE; subst...
    assert (univ = true) by csetdec; subst.
    apply subcapt_universal...
  - Case "subcapt_in".
    dependent induction SDE...
    assert (x = x0) by fsetdec; subst.
    eapply subcapt_var...
  - Case "subcapt_in_univ".
    dependent induction SDE; eauto using subcapt_universal.
  - Case "subcapt_var".
    apply subcapt_set...
    + intros x xIn...
    + destruct b...
      destruct univ... 
      destruct D; simpl in *; subst.
      inversion SDE...
Qed.

(* Needed, line 664 *)
(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall x D Q C Δ Γ C1 C2 ,
  (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ₛ C1 <: C2 ->
  (* (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ wf -> *)
  Γ ⊢ₛ C <: D ->
  (map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C C1) <: (subst_cset x C C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec.
  eauto 4 using wf_env_subst_cb, wf_cset_subst_cb, wf_cset_weaken_head.
  intros x D T C Δ Γ C1 C2 C1subC2 CsubD.
  remember (Δ ++ [(x, bind_typ (D # T))] ++ Γ).
  generalize dependent Δ.
  induction C1subC2; intros G ET; subst; simpl subst_cse; eauto.
  - apply subcapt_regular in CsubD; destruct CsubD. destruct H2.
    eapply subcset_top. eapply wf_env_subst_cb...
    eapply wf_cset_subst_cb. apply H0. apply H. auto.
  - apply subcapt_regular in CsubD; destruct CsubD. destruct H2.
    eapply subcset_bot. eapply wf_env_subst_cb... auto. eapply wf_cset_subst_cb.
    apply H0. assumption. assumption.
  - apply subcapt_regular in CsubD; destruct CsubD. destruct H2.
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
        eapply wf_env_subst_cb. apply subcapt_regular in C1subC2.
        destruct C1subC2. apply H0. apply subcapt_regular in CsubD.
        destruct CsubD as [H0 [H1 H2]]...
      * rewrite (subst_cse_fresh X D C).
        -- binds_cases H.
        ++ simpl in Fr0. fsetdec. (* X in Γ *)
        ++ inversion H0. subst. apply IHC1subC2... (* X in [(X, bind_typ (D # T))] *)
        ++ (* X in G, contradiciton, environment is not ok *)
           assert (wf_env (G ++ [(X, bind_typ (D # T))] ++ Γ)) as Hwf.
           { apply subcapt_regular in C1subC2. destruct C1subC2 as [hwf _]... }
           apply ok_from_wf_env in Hwf.
           apply fresh_mid_head in Hwf.
           apply binds_In in H1.
           unfold not in Hwf. apply Hwf in H1. inversion H1.
        -- apply (notin_fv_wf_cse Γ).
          ++ apply subcapt_regular in CsubD. destruct CsubD as [_ [_ Dwf]]...
          ++ assert (wf_env (G ++ [(X, bind_typ (D # T))] ++ Γ)).
             { apply subcapt_regular in C1subC2. destruct C1subC2 as [hwf _]... }
             apply ok_from_wf_env in H0.
             apply fresh_mid_tail in H0. assumption.
    + binds_cases H.
      * apply (subcset_trans_var (subst_cse x C R) (map (subst_cb x C) G ++ Γ) (subst_cse x C Q) X (subst_ct x C T0)).
        -- apply binds_tail.
          ++ rewrite (map_subst_cb_id Γ x C).
             apply binds_map with (f:=(subst_cb x C)) in H. simpl in H...
             apply subcapt_regular in CsubD. destruct CsubD...
             apply subcapt_regular in C1subC2. destruct C1subC2 as [Hwf _].
             apply ok_from_wf_env in Hwf. apply fresh_mid_tail in Hwf... 
          ++ rewrite dom_map...
        -- apply IHC1subC2... 
      * assert ((map (subst_cb x C) G ++ Γ) ⊢ₛ cse_fvar X <: subst_cse x C R).
        { apply (subcset_trans_var (subst_cse x C R) (map (subst_cb x C) G ++ Γ) (subst_cse x C R) X (subst_ct x C T0)).
          - assert (HH := H1).  
            apply binds_map with (f:=(subst_cb x C)) in H1. simpl in H1.
            apply subcapt_regular in C1subC2. destruct C1subC2 as [Hwf _].
            apply ok_from_wf_env in Hwf. apply ok_remove_mid in Hwf.
            apply binds_head with (E:=Γ) in H1...
          - assert (HH := IHC1subC2 G).
            apply subcapt_regular in HH. destruct HH as [HH1 [HH2 HH3]].
            apply subcapt_reflexivity.
            auto. auto. auto. 
        }
        eapply subcapt_transitivity. apply H. apply IHC1subC2...
  - constructor...
    eapply wf_cset_subst_cb. apply H.
    apply subcapt_regular in C1subC2.
    destruct C1subC2 as [wf1 [wf2 wf3]]...
    apply subcapt_regular in CsubD.
    destruct CsubD as [wf1 [wf2 wf3]]...
  - apply subcset_join_inr...
    eapply wf_cset_subst_cb. apply H.
    apply subcapt_regular in C1subC2.
    destruct C1subC2 as [wf1 [wf2 wf3]]...
    apply subcapt_regular in CsubD.
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
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ wf ->
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ C <: D ->
  Γ ⊢ P <: Q ->
  (map (subst_tb X P) Δ ++ Γ) ⊢ₛ C <: D.
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb, wf_typ_subst_tb with fsetdec.
  intros * WfEnv Subcapt Sub.
  assert (PureQ : pure_type Q).
  { eapply wf_env_tail in WfEnv.
    inversion WfEnv...
  }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ Sub) PureQ)).
  assert ((map (subst_tb X P) Δ ++ Γ) ⊢ wf).
  { eapply wf_env_subst_tb... apply sub_regular in Sub. destruct Sub as [_[H1 _]]... }
  generalize dependent P.
  dependent induction Subcapt; intros P Sub PureP WfEnvSubst.
  - Case "subcset_top".
    apply subcset_top.
    + admit.
    + eapply wf_cset_subst_tb... apply sub_regular in Sub. destruct Sub as [_[H1 _]]...
  - apply subcset_bot...
    inversion H0; subst...
    admit. admit.
  - apply subcapt_reflexivity...
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
