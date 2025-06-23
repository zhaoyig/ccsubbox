Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Import Lia.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.
Require Import CCsub_Red.
Require Import CCsub_Inversion.
Require Import CCsub_RuntimeInversion.

Lemma loc_transform_ctx_wf : forall E S Δ Δ' Γ,
  env_well_typed S E Γ ->
  wf_ctx (Δ ++ Γ) S ->
  loc_transform_ctx E Δ Δ' ->
  wf_ctx Δ' S.
Proof with eauto.
  intros * EnvTyp WfCtx LocTrans.
  generalize dependent Γ.
  dependent induction LocTrans; intros; subst; simpl in *...
  { inverts EnvTyp; simpl_env in WfCtx... }
  inverts EnvTyp.
  eapply IHLocTrans...
  eapply wf_ctx_subst_cb...
Qed.

Lemma loc_transform_cse_ident : forall E C,
  cse_fvars C = {}A ->
  loc_transform_cse E C C.
Proof with eauto.
  intros * Fv.
  induction E...
  destruct a as [x l].
  assert (x `notin` cse_fvars C) by (rewrite Fv; fsetdec).
  apply loc_transform_cse_multi with (E := E) (C := C)...
  simpl_env.
  rewrite <- subst_cse_fresh...
Qed.

Lemma loc_transform_cse_result : forall C E,
  exists C2, loc_transform_cse E C C2.
Proof with eauto*.
  intros.
  generalize dependent C.
  dependent induction E; intros...
  destruct a as [x l].
  pose proof (IHE (subst_cse x (cse_loc l) C)) as [C2 LocTrans].
  exists C2...
Qed.

Lemma loc_transform_cse_deterministic : forall E C1 C2 C3,
  loc_transform_cse E C1 C2 ->
  loc_transform_cse E C1 C3 ->
  C2 = C3.
Proof with eauto*.
  intros * LocTrans1 LocTrans2.
  generalize dependent C3.
  dependent induction LocTrans1; intros; subst; simpl in *.
  - inversion LocTrans2; subst...
  - inversion LocTrans2; subst...
Qed.

Lemma loc_transform_ident : forall E T,
  fv_ct T = {}A ->
  loc_transform E T T.
Proof with eauto.
  intros * Fv.
  induction E...
  destruct a as [x l].
  assert (x `notin` fv_ct T) by (rewrite Fv; fsetdec).
  apply loc_transform_multi with (E := E) (T := T)...
  rewrite <- subst_ct_fresh...
Qed.

Lemma loc_transform_deterministic : forall E T1 T2 T3,
  loc_transform E T1 T2 ->
  loc_transform E T1 T3 ->
  T2 = T3.
Proof with eauto*.
  intros * LocTrans1 LocTrans2.
  generalize dependent T3.
  dependent induction LocTrans1; intros; subst; simpl in *.
  1,2: inversion LocTrans2; subst...
Qed.

Lemma loc_transform_result : forall T E,
  exists T2, loc_transform E T T2.
Proof with eauto*.
  intros *.
  generalize dependent T.
  dependent induction E; intros; simpl in *.
  - exists T...
  - destruct a as [x l].
    pose proof (IHE (subst_ct x (cse_loc l) T)) as [T2 LocTrans].
    exists T2...
Qed.

Lemma loc_transform_pure : forall E T1 T2,
  loc_transform E T1 T2 ->
  pure_type T1 ->
  pure_type T2.
Proof with eauto.
  intros * LocTrans Pure.
  dependent induction LocTrans; intros; subst; simpl in *.
  - apply Pure.
  - apply IHLocTrans.
    eapply subst_ct_pure_type in Pure...
Qed.

Lemma subst_ct_invert_capt : forall T C R D x,
  subst_ct x D T = C # R ->
  exists C' R', T = C' # R' /\ C = subst_cse x D C' /\ R = subst_ct x D R'.
Proof with eauto*.
  intros * Eq.
  generalize dependent C.
  generalize dependent R.
  induction T; simpl in *; intros...
  destruct v...
  exists c, T; repeat split...
Qed.

Lemma loc_transform_capt : forall E C R T,
  loc_transform E (C # R) T ->
  exists C' R', T = C' # R' /\ loc_transform_cse E C C' /\ loc_transform E R R'.
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans...
  destruct (IHLocTrans (subst_cse x (cse_loc l) C) (subst_ct x (cse_loc l) R) eq_refl) as [C0 [R0 [Eq [LocTransC LocTransR]]]]; subst...
  exists C0, R0; repeat split...
Qed.

Lemma loc_tranform_equiv : forall E C R C' R',
  loc_transform E (C # R) (C' # R') <->
  (loc_transform E R R' /\ loc_transform_cse E C C').
Proof with eauto*.
  intros *.
  split; intros LocTrans.
  - dependent induction LocTrans; simpl in *...
    destruct (IHLocTrans (subst_cse x (cse_loc l) C) (subst_ct x (cse_loc l) R) C' R') as [LocTransR LocTransC]; subst...
  - destruct LocTrans as [LocTransR LocTransC].
    generalize dependent C.
    generalize dependent C'.
    dependent induction LocTransR; intros; subst; simpl in *...
    + dependent induction LocTransC...
    + dependent induction LocTransC; simpl in *...
Qed.

Lemma loc_transform_cse_wf_nil : forall C1 C2 Γ S E,
  env_well_typed S E Γ ->
  wf_cse Γ S C1 ->
  loc_transform_cse E C1 C2 ->
  wf_cse nil S C2.
Proof with eauto.
  intros * EnvTyp WfCse LocTrans.
  generalize dependent Γ.
  dependent induction LocTrans; simpl in *; eauto; intros Γ EnvTyp WfCse; subst.
  - inverts EnvTyp...
  - inversion EnvTyp; subst.
    eapply IHLocTrans; eauto.
    rewrite_env (nil ++ [(x, bind_typ (cse_loc l # R))] ++ Γ0) in WfCse.
    epose proof (env_well_typed_ctx_wf _ _ _ H3).
    epose proof (wf_cse_over_subst _ nil _ _ (cse_loc l) C _)...
    simpl in *...
    apply H0...
Qed.

Lemma bind_typ_capt : forall x Γ S T,
  wf_ctx Γ S ->
  binds x (bind_typ T) Γ ->
  exists C R,
    T = C # R.
Proof with eauto*.
  intros * WfCtx Binds.
  dependent induction WfCtx; intros; simpl in *.
  - inversion Binds.
  - simpl_env in Binds.
    binds_cases Binds; subst; simpl in *.
    destruct (IHWfCtx H2) as [C [R Eq]]; subst...
  - simpl_env in Binds.
    binds_cases Binds; subst; simpl in *.
    destruct (IHWfCtx H1) as [C1 [R1 Eq]]; subst...
    inverts H3...
Qed.

Lemma runtime_ctx_binds_loc : forall Γ E S x C R,
  env_well_typed S E Γ ->
  binds x (bind_typ (C # R)) Γ ->
  exists l, binds x l E /\ C = cse_loc l.
Proof with eauto*.
  intros * EnvTyp Binds.
  dependent induction EnvTyp; intros; simpl in *.
  { inversion Binds. }
  simpl_env in Binds.
  binds_cases Binds; subst; simpl in *.
  - destruct (IHEnvTyp H1) as [l0 [BindsL0 Eq]]; subst.
    exists l0; split...
    simpl_env.
    eapply binds_tail...
  - inverts H3.
    exists l; split...
    simpl_env.
    eapply binds_head...
Qed.

Lemma wf_cse_empty_means_no_fvars : forall C S,
  wf_cse nil S C ->
  cse_fvars C = {}A.
Proof with eauto.
  intros * WfCse.
  dependent induction WfCse; simpl in *; eauto.
  - inversion H.
  - rewrite IHWfCse1, IHWfCse2...
    fsetdec...
Qed.

Lemma wf_typ_empty_means_no_fvars : forall T S,
  wf_typ nil S T ->
  fv_ct T = {}A.
Proof with eauto.
  intros * WfTyp.
  enough (fv_ct T `subset` {}A) by fsetdec.
  unfold AtomSet.F.Subset in *.
  intros.
  epose proof (wf_typ_notin_fv_ct a _ _ _ WfTyp)...
  simpl in *.
  assert (a `in` fv_ct T -> a `in` {}A) by fsetdec...
Qed.

Lemma loc_transform_cse_join : forall E C1 C2 C1' C2',
  loc_transform_cse E C1 C1' ->
  loc_transform_cse E C2 C2' ->
  loc_transform_cse E (cse_join C1 C2) (cse_join C1' C2').
Proof with eauto.
  intros * LocTrans1 LocTrans2.
  generalize dependent C2.
  generalize dependent C2'.
  dependent induction LocTrans1; intros; subst; simpl in *...
  - inversion LocTrans2; subst...
  - inversion LocTrans2; subst...
Qed.

Lemma loc_transform_cse_bound_fvar : forall E x l,
  binds x l E ->
  loc_transform_cse E (cse_fvar x) (cse_loc l).
Proof with eauto.
  intros * Binds.
  induction E; simpl in *...
  { inversion Binds. }
  destruct a as [y l'].
  simpl_env in Binds.
  binds_cases Binds; subst; simpl in *.
  - assert (x <> y) by fsetdec.
    constructor...
    rewrite <- subst_cse_fresh...
  - constructor...
    simpl...
    destruct (x == x); try fsetdec...
    epose proof (loc_transform_cse_ident E (cse_loc l'))...
Qed.

Lemma loc_transform_cse_unbound_fvar : forall E x,
  x `notin` dom E ->
  loc_transform_cse E (cse_fvar x) (cse_fvar x).
Proof with eauto.
  intros * NotIn.
  induction E; simpl in *...
  destruct a as [y l].
  assert (x <> y) by fsetdec.
  constructor...
  rewrite <- subst_cse_fresh...
Qed.

Ltac loc_transform_cse_ident_eq H :=
  match type of H with
  | loc_transform_cse ?E ?C ?C' =>
      unshelve epose proof (loc_transform_cse_deterministic _ _ _ _ H (loc_transform_cse_ident E C _)); subst
  end.

Lemma loc_transform_ctx_binds : forall E Δ Δ' x T U,
  x `notin` dom E ->
  loc_transform_ctx E Δ Δ' ->
  binds x (bind_typ T) Δ ->
  loc_transform E T U ->
  binds x (bind_typ U) Δ'.
Proof with eauto.
  intros * NotIn LocTrans Binds LocTransT.
  generalize dependent T.
  generalize dependent U.
  dependent induction LocTrans; intros; subst; simpl in *; inverts LocTransT...
  destruct (x == x0); try fsetdec...
  assert (x `notin` dom E) by fsetdec.
  eapply IHLocTrans; eauto.
  replace (bind_typ (subst_ct x0 (cse_loc l) T)) with (subst_cb x0 (cse_loc l) (bind_typ T))...
Qed.

Lemma loc_transform_cse_wf : forall Γ Δ Δ' E S C1 C2,
  env_well_typed S E Γ ->
  wf_ctx (Δ ++ Γ) S ->
  wf_cse (Δ ++ Γ) S C1 ->
  loc_transform_cse E C1 C2 ->
  loc_transform_ctx E Δ Δ' ->
  wf_cse Δ' S C2.
Proof with eauto.
  intros * EnvTyp WfCtx WfCse LocTrans LocTransCtx.
  assert (WfΓ : wf_ctx Γ S) by (eapply env_well_typed_ctx_wf; eauto).
  generalize dependent C2.
  generalize dependent Δ'.
  generalize dependent E.
  dependent induction WfCse; intros; subst; simpl in *.
  1,3,5: loc_transform_cse_ident_eq LocTrans...
  - apply ok_from_wf_ctx in WfCtx.
    binds_cases H; subst.
    + destruct (bind_typ_capt _ _ _ _ WfΓ H0) as [C [R Eq]]; subst.
      unshelve epose proof (runtime_ctx_binds_loc Γ) as [l [BindsL EqL]]...
      subst.
      epose proof (loc_transform_cse_bound_fvar _ _ _ BindsL) as LocTransFvar.
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans LocTransFvar); subst...
      destruct ((proj2 (env_typing_inversion _ _ _ _ _ _ EnvTyp BindsL)) H0)...
    + assert (NotIn: x `notin` dom Γ). {
        eapply head_not_in_tail...
        apply binds_In in H1...
      }
      erewrite <- env_well_typed_preserves_dom in NotIn...
      epose proof (loc_transform_cse_unbound_fvar _ _ NotIn) as Ident.
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans Ident); subst...
      epose proof (loc_transform_result T E) as [T' LocTransT']...
      eapply loc_transform_ctx_binds in H1...
  - epose proof (loc_transform_cse_result Q1 E) as [Q1' LocTransQ1].
    epose proof (loc_transform_cse_result Q2 E) as [Q2' LocTransQ2].
    epose proof (loc_transform_cse_join _ _ _ _ _ LocTransQ1 LocTransQ2) as LocTransJoin.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans LocTransJoin); subst.
    constructor.
    eapply IHWfCse1...
    eapply IHWfCse2...
Qed.

Lemma subcapt_under_loc_transform : forall Γ E S C1 C2 C1' C2',
  env_well_typed S E Γ ->
  loc_transform_cse E C1 C1' ->
  loc_transform_cse E C2 C2' ->
  subcapt Γ S C1 C2 ->
  subcapt nil S C1' C2'.
Proof with eauto*.
  intros * EnvTyp LocTrans1 LocTrans2 Subcapt.
  generalize dependent C1'.
  generalize dependent C2'.
  generalize dependent E.
  dependent induction Subcapt; intros.
  - loc_transform_cse_ident_eq LocTrans2...
    constructor...
    eapply loc_transform_cse_wf_nil...
  - loc_transform_cse_ident_eq LocTrans1...
    constructor...
    eapply loc_transform_cse_wf_nil...
  - assert (X `in` dom E). {
     epose proof (wf_cse_fvars_from_ctx _ _ _ X H0).
     erewrite <- env_well_typed_preserves_dom in H1...
     simpl in *...
     fsetdec.
    }
    dependent induction EnvTyp; simpl in *; try fsetdec.
    destruct (x == X) eqn:Eq; subst.
    + inverts LocTrans1.
      simpl in *.
      destruct (X == X) eqn:Eq'; subst...
      inverts LocTrans2.
      simpl in *.
      destruct (X == X); subst...
      loc_transform_cse_ident_eq H9...
      loc_transform_cse_ident_eq H10...
    + inverts LocTrans1.
      simpl in *.
      destruct (x == X); subst...
      inverts LocTrans2.
      simpl in *.
      destruct (x == X); subst...
      assert (X `in` dom E) by fsetdec.
      apply IHEnvTyp...
      inverts H...
      rewrite_nil_concat.
      eapply wf_cse_strengthen...
      simpl...
  - unshelve epose proof (loc_transform_cse_ident E (cse_loc l) _) as Ident...
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans1 Ident); subst...
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans2 Ident); subst...
    apply subcapt_reflexivity...
    inverts H0...
  - destruct (subcapt_regular _ _ _ _ Subcapt) as [_ [_ [WfR _]]].
    unshelve epose proof (loc_transform_cse_result R E) as [CR LocCR]...
    assert (subcapt Γ S (cse_fvar X) R). {
      eapply subcapt_trans_var...
      eapply subcapt_reflexivity...
    }
    destruct (runtime_ctx_binds_loc _ _ _ _ _ _ EnvTyp H) as [l [BindsL Eq]]; subst.
    apply subcapt_transitivity with (Q := CR)...
    loc_transform_cse_ident_eq LocCR...
    epose proof (loc_transform_cse_bound_fvar _ _ _ BindsL).
    epose proof (loc_transform_cse_deterministic _ _ _ _ H1 LocTrans1); subst...
    eapply subcapt_reflexivity...
    epose proof ((proj2 (env_typing_inversion _ _ _ _ _ _ EnvTyp BindsL)) H).
    destruct H2 as [R' StoreBinds]...
  - loc_transform_cse_ident_eq LocTrans1...
    destruct (subcapt_regular _ _ _ _ Subcapt) as [_ [_ [WfR _]]].
    unshelve epose proof (loc_transform_cse_result R E) as [CR LocCR]...
    apply subcapt_transitivity with (Q := CR)...
    assert (WfS : wf_store_ctx S) by (eapply env_well_typed_store_ctx_wf; eauto).
    assert (WfRT: wf_typ nil S (R # T)) by (eapply wf_typ_from_wf_store_ctx_nil; eauto).
    inverts WfRT.
    loc_transform_cse_ident_eq LocCR...
    epose proof (wf_cse_empty_means_no_fvars _ _ H2)...
    eapply subcapt_trans_loc...
    eapply subcapt_reflexivity...
  - destruct (loc_transform_cse_result R2 E) as [CR2 LocTransCR2].
    assert (WfR1 : wf_cse Γ S R1) by applys subcapt_regular Subcapt.
    destruct (loc_transform_cse_result R1 E) as [CR1 LocTransCR1].
    assert (C2' = cse_join CR1 CR2); subst. {
      applys loc_transform_cse_deterministic...
      eapply loc_transform_cse_join...
    }
    apply subcapt_join_inl...
    eapply loc_transform_cse_wf_nil with (C1 := R2)...
  - destruct (loc_transform_cse_result R1 E) as [CR1 LocTransCR1].
    assert (WfR2 : wf_cse Γ S R2) by applys subcapt_regular Subcapt.
    destruct (loc_transform_cse_result R2 E) as [CR2 LocTransCR2].
    assert (C2' = cse_join CR1 CR2); subst. {
      applys loc_transform_cse_deterministic...
      eapply loc_transform_cse_join...
    }
    apply subcapt_join_inr...
    eapply loc_transform_cse_wf_nil with (C1 := R1)...
  - assert (WfR1 : wf_cse Γ S R1) by applys subcapt_regular Subcapt1.
    assert (WfR2 : wf_cse Γ S R2) by applys subcapt_regular Subcapt2.
    destruct (loc_transform_cse_result R1 E) as [CR1 LocTransCR1].
    destruct (loc_transform_cse_result R2 E) as [CR2 LocTransCR2].
    assert (C1' = cse_join CR1 CR2); subst. {
      applys loc_transform_cse_deterministic...
      eapply loc_transform_cse_join...
    }
    apply subcapt_join_elim...
Qed.

Lemma subcapt_under_loc_transform_strong : forall Γ Δ Δ' E S C1 C2 C1' C2',
  env_well_typed S E Γ ->
  subcapt (Δ ++ Γ) S C1 C2 ->
  loc_transform_cse E C1 C1' ->
  loc_transform_cse E C2 C2' ->
  loc_transform_ctx E Δ Δ' ->
  subcapt Δ' S C1' C2'.
Proof with eauto*.
  intros * EnvTyp Subcapt LocTransC1 LocTransC2 LocTransCtx.
  generalize dependent C1'.
  generalize dependent C2'.
  generalize dependent E.
  generalize dependent Δ'.
  dependent induction Subcapt; intros.
  - loc_transform_cse_ident_eq LocTransC2...
    constructor...
    eapply loc_transform_ctx_wf...
    eapply loc_transform_cse_wf...
Admitted.


Definition no_type_bindings (Γ : ctx) : Prop :=
  forall X U, ~ binds X (bind_sub U) Γ.

Lemma runtime_ctx_no_type_bindings : forall Γ E S,
  env_well_typed S E Γ ->
  no_type_bindings Γ.
Proof with eauto*.
  intros * EnvTyp.
  unfold no_type_bindings.
  dependent induction EnvTyp; intros; intro...
  - inversion H0.
  - binds_cases H1...
Qed.

(* Lemma subst_ct_invert_fun : forall T U C R D x, *)
(*   subst_ct x D U = ∀ (C # R) T -> *)
(*   exists C' R' T', *)
(*     U = ∀ (C' # R') T' /\ C = subst_cse x D C' /\ R = subst_ct x D R'. *)
(* Proof with eauto*. *)
(*   intros * Eq. *)
(*   generalize dependent C. *)
(*   generalize dependent R. *)
(*   generalize dependent T. *)
(*   induction U; simpl in *; intros; subst... *)
(*   destruct v... *)
(*   inverts Eq. *)
(*   destruct (subst_ct_invert_capt _ _ _ _ x H0) as [C' [R' [Eq1 [Eq2 Eq3]]]]; subst... *)
(*   exists C', R', U2; repeat split... *)
(* Qed. *)

Lemma loc_transform_fun : forall E C1 R1 T1 U,
  loc_transform E (∀ (C1 # R1) T1) U ->
  exists C2 R2 T2,
    loc_transform_cse E C1 C2 /\
    loc_transform E R1 R2 /\
    loc_transform E T1 T2 /\
    U = ∀ (C2 # R2) T2.
Proof with eauto*.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists C1, R1, T1; repeat split...
  - destruct (IHLocTrans _ _ _ eq_refl) as [C2 [R2 [T2 [LocTransC [LocTransR [LocTransT Eq]]]]]]; subst.
    exists C2, R2, T2; repeat split...
Qed.

Lemma loc_transform_tfun : forall E R1 T1 U,
  loc_transform E (∀ [R1] T1) U ->
  exists R2 T2,
    loc_transform E R1 R2 /\
    loc_transform E T1 T2 /\
    U = ∀ [R2] T2.
Proof with eauto*.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists R1, T1; split...
  - destruct (IHLocTrans _ _ eq_refl) as [R2 [T2 [LocTransR LocTransT]]]; subst.
    exists R2, T2; split...
Qed.

Lemma loc_transform_box : forall E T1 U,
  loc_transform E (typ_box T1) U ->
  exists T2, loc_transform E T1 T2 /\ U = typ_box T2.
Proof with eauto*.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists T1; split... 
  - destruct (IHLocTrans _ eq_refl) as [T2 [LocTransT2 Eq]]; subst.
    exists T2; split...
Qed.

Lemma sub_under_loc_transform : forall Γ E S T1 T2 T1' T2',
  env_well_typed S E Γ ->
  loc_transform E T1 T1' ->
  loc_transform E T2 T2' ->
  sub Γ S T1 T2 ->
  sub nil S T1' T2'.
Proof with eauto using subcapt_under_loc_transform, loc_transform_pure.
  intros * EnvTyp LocTrans1 LocTrans2 Sub.
  generalize dependent T1'.
  generalize dependent T2'.
  generalize dependent E.
  dependent induction Sub; intros.
  - exfalso. inverts H0.
    epose proof (runtime_ctx_no_type_bindings _ _ _ EnvTyp) as NoTypeBinds.
    specialize (NoTypeBinds X T)...
  - exfalso.
    epose proof (runtime_ctx_no_type_bindings _ _ _ EnvTyp) as NoTypeBinds.
    specialize (NoTypeBinds X U)...
  - unshelve epose proof (loc_transform_capt _ _ _ _ LocTrans1) as [C1' [R1' [Eq1 [LocTransC1 LocTransR1]]]]; subst.
    unshelve epose proof (loc_transform_capt _ _ _ _ LocTrans2) as [C2' [R2' [Eq2 [LocTransC2 LocTransR2]]]]; subst.
    destruct ((proj1 (loc_tranform_equiv _ _ _ _ _)) LocTrans1).
    destruct ((proj1 (loc_tranform_equiv _ _ _ _ _)) LocTrans2).
    constructor...
  - epose proof (fv_loc_transform_nil _ _ _ _ _ EnvTyp H0 LocTrans1).
    enough (T2' = typ_top); subst...
    unshelve epose proof (loc_transform_ident E typ_top _)...
    epose proof (loc_transform_deterministic _ _ _ _ LocTrans2 H3)...
  - destruct (loc_transform_fun _ _ _ _ _ LocTrans1) as [C1r [R1r [T1r [LocTransC1 [LocTransR1 [LocTransT1 Eq]]]]]]; subst.
    destruct (loc_transform_fun _ _ _ _ _ LocTrans2) as [C2r [R2r [T2r [LocTransC2 [LocTransR2 [LocTransT2 Eq']]]]]]; subst.
    pick fresh x and apply sub_arr; simpl...
    admit.
  - destruct (loc_transform_tfun _ _ _ _ LocTrans1) as [R1r [T1r [LocTransR1 [LocTransT1 Eq]]]]; subst.
    destruct (loc_transform_tfun _ _ _ _ LocTrans2) as [R2r [T2r [LocTransR2 [LocTransT2 Eq']]]]; subst.
    pick fresh x and apply sub_all; simpl...
    admit.
  - epose proof (loc_transform_box _ _ _ LocTrans1) as [T1r [LocTransT1 Eq]]; subst.
    epose proof (loc_transform_box _ _ _ LocTrans2) as [T2r [LocTransT2 Eq']]; subst.
    constructor...
Admitted.
    eapply subcapt_trans_loc...
    eapply subcapt_reflexivity...
