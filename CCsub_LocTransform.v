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
  { inversion EnvTyp; subst; simpl_env in WfCtx... }
  inversion EnvTyp; subst.
  eapply IHLocTrans...
  eapply wf_ctx_subst_cb...
Qed.

Lemma loc_transform_cse_ident : forall E C,
  (forall x, x `notin`A cse_fvars C) ->
  loc_transform_cse E C C.
Proof with eauto.
  intros * Fv.
  induction E...
  destruct a as [x l].
  apply loc_transform_cse_multi with (E := E) (C := C)...
  simpl_env.
  rewrite <- subst_cse_fresh...
Qed.

Lemma loc_transform_cse_result : forall C E,
  exists C2, loc_transform_cse E C C2.
Proof with eauto.
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
Proof with eauto.
  intros * LocTrans1 LocTrans2.
  generalize dependent C3.
  dependent induction LocTrans1; intros; subst; simpl in *.
  - inversion LocTrans2; subst...
  - inversion LocTrans2; subst...
Qed.

Lemma loc_transform_ident : forall E T,
  (forall x, x `notin`A fv_ct T) ->
  loc_transform E T T.
Proof with eauto.
  intros * Fv.
  induction E...
  destruct a as [x l].
  apply loc_transform_multi with (E := E) (T := T)...
  rewrite <- subst_ct_fresh...
Qed.

Lemma loc_transform_deterministic : forall E T1 T2 T3,
  loc_transform E T1 T2 ->
  loc_transform E T1 T3 ->
  T2 = T3.
Proof with eauto.
  intros * LocTrans1 LocTrans2.
  generalize dependent T3.
  dependent induction LocTrans1; intros; subst; simpl in *.
  1,2: inversion LocTrans2; subst...
Qed.

Lemma loc_transform_result : forall T E,
  exists T2, loc_transform E T T2.
Proof with eauto.
  intros *.
  generalize dependent T.
  dependent induction E; intros; simpl in *.
  - exists T...
  - destruct a as [x l].
    pose proof (IHE (subst_ct x (cse_loc l) T)) as [T2 LocTrans].
    exists T2...
Qed.

Lemma loc_transform_exp_ident : forall E e,
  (forall x, x `notin`A fv_ve e `union`A fv_ce e) ->
  loc_transform_exp E e e.
Proof with eauto.
  intros * Fv.
  induction E...
  destruct a as [x l].
  apply loc_transform_exp_multi with (E := E) (e1 := e)...
  rewrite <- subst_ve_fresh...
Qed.

Lemma loc_transform_exp_deterministic : forall E e1 e2 e3,
  loc_transform_exp E e1 e2 ->
  loc_transform_exp E e1 e3 ->
  e2 = e3.
Proof with eauto.
  intros * LocTrans1 LocTrans2.
  generalize dependent e3.
  dependent induction LocTrans1; intros; subst; simpl in *;
  inversion LocTrans2; subst...
Qed.

Lemma loc_transform_exp_result : forall e E,
  exists e2, loc_transform_exp E e e2.
Proof with eauto.
  intros *.
  generalize dependent e.
  dependent induction E; intros; simpl in *.
  - exists e...
  - destruct a as [x l].
    pose proof (IHE (subst_ve x l (cse_loc l) e)) as [e2 LocTrans].
    exists e2...
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
Proof with eauto.
  intros * Eq.
  generalize dependent C.
  generalize dependent R.
  induction T; simpl in *; intros; try inversion Eq...
  destruct v; inversion Eq.
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

Lemma loc_transform_equiv : forall E C R C' R',
  loc_transform E (C # R) (C' # R') <->
  (loc_transform E R R' /\ loc_transform_cse E C C').
Proof with eauto.
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
  - inversion EnvTyp; subst...
  - inversion EnvTyp; subst.
    eapply IHLocTrans; eauto.
    rewrite_env (nil ++ [(x, bind_typ (cse_loc l # R))] ++ Γ0) in WfCse.
    epose proof (env_well_typed_ctx_wf _ _ _ H3).
    epose proof (wf_cse_over_subst _ nil _ _ (cse_loc l) C _)...
    simpl in *...
    apply H0...
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
  uniq E ->
  binds x l E ->
  loc_transform_cse E (cse_fvar x) (cse_loc l).
Proof with eauto.
  intros * Uniq Binds.
  induction E; simpl in *...
  { inversion Binds. }
  destruct a as [y l'].
  simpl_env in Binds.
  analyze_binds Binds.
  - constructor...
    simpl...
    destruct (y == y); try fsetdec...
    epose proof (loc_transform_cse_ident E (cse_loc l'))...
  - inversion Uniq; subst.
    constructor...
    rewrite <- subst_cse_fresh...
    simpl.
    enough (y <> x) by fsetdec.
    intro; subst...
Qed.

Lemma loc_transfrom_exp_bound_fvar : forall E x l,
  uniq E ->
  binds x l E ->
  loc_transform_exp E x l.
Proof with eauto.
  intros * Uniq Binds.
  induction E; simpl in *...
  { inversion Binds. }
  destruct a as [y l'].
  simpl_env in Binds.
  analyze_binds Binds.
  - constructor...
    simpl...
    destruct (y == y); try fsetdec...
    epose proof (loc_transform_exp_ident E l')...
  - inversion Uniq; subst.
    constructor...
    rewrite <- subst_ve_fresh...
    simpl.
    enough (y <> x) by fsetdec.
    intro; subst...
Qed.

Lemma loc_transform_cse_unbound_fvar : forall E x,
  x `notin`A dom E ->
  loc_transform_cse E (cse_fvar x) (cse_fvar x).
Proof with eauto.
  intros * NotIn.
  induction E; simpl in *...
  destruct a as [y l].
  assert (x <> y) by fsetdec.
  constructor...
  rewrite <- subst_cse_fresh...
Qed.

Lemma loc_transform_exp_unbound_var : forall E x,
  x `notin`A dom E ->
  loc_transform_exp E x x.
Proof with eauto.
  intros * NotIn.
  induction E; simpl in *...
  destruct a as [y l].
  assert (x <> y) by fsetdec.
  constructor...
  rewrite <- subst_ve_fresh...
Qed.

Ltac loc_transform_cse_ident_eq H :=
  match type of H with
  | loc_transform_cse ?E ?C ?C' =>
      unshelve epose proof (loc_transform_cse_deterministic _ _ _ _ H (loc_transform_cse_ident E C _)); subst
  end.

Ltac loc_transform_ident_eq H :=
  match type of H with
  | loc_transform ?E ?T ?T' =>
      unshelve epose proof (loc_transform_deterministic _ _ _ _ H (loc_transform_ident E T _)); subst
  end.

Ltac loc_transform_exp_ident_eq H :=
  match type of H with
  | loc_transform_exp ?E ?e ?e' =>
      unshelve epose proof (loc_transform_exp_deterministic _ _ _ _ H (loc_transform_exp_ident E e _)); subst
  end.

Lemma loc_transform_unbound_var : forall E X,
  X `notin`A dom E ->
  loc_transform E X X.
Proof with eauto.
  intros * NotIn.
  induction E; simpl in *...
  destruct a as [y l].
  assert (X <> y) by fsetdec.
  constructor...
Qed.

Lemma loc_transform_ctx_binds_typ : forall E Δ Δ' x T U,
  x `notin`A dom E ->
  loc_transform_ctx E Δ Δ' ->
  binds x (bind_typ T) Δ ->
  loc_transform E T U ->
  binds x (bind_typ U) Δ'.
Proof with eauto.
  intros * NotIn LocTrans Binds LocTransT.
  generalize dependent T.
  generalize dependent U.
  dependent induction LocTrans; intros; subst; simpl in *; inversion LocTransT; subst...
  destruct (x == x0); try fsetdec...
  assert (x `notin`A dom E) by fsetdec.
  eapply IHLocTrans; eauto.
  replace (bind_typ (subst_ct x0 (cse_loc l) T)) with (subst_cb x0 (cse_loc l) (bind_typ T))...
Qed.

Lemma loc_transform_ctx_binds_sub : forall E Δ Δ' x T U,
  x `notin`A dom E ->
  loc_transform_ctx E Δ Δ' ->
  binds x (bind_sub T) Δ ->
  loc_transform E T U ->
  binds x (bind_sub U) Δ'.
Proof with eauto.
  intros * NotIn LocTrans Binds LocTransT.
  generalize dependent T.
  generalize dependent U.
  dependent induction LocTrans; intros; subst; simpl in *; inversion LocTransT; subst...
  destruct (x == x0); try fsetdec...
  assert (x `notin`A dom E) by fsetdec.
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
  - apply uniq_from_wf_ctx in WfCtx.
    analyze_binds_uniq H; subst.
    + erewrite <- env_well_typed_preserves_dom in H0...
      epose proof (loc_transform_cse_unbound_fvar _ _ H0) as Ident.
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans Ident); subst...
      epose proof (loc_transform_result T E) as [T' LocTransT']...
      econstructor...
      eapply loc_transform_ctx_binds_typ in BindsTac...
    + destruct (bind_typ_capt _ _ _ _ WfΓ BindsTac) as [C [R Eq]]; subst.
      unshelve epose proof (runtime_ctx_binds_loc Γ _ _ _ _ R) as [l [BindsL EqL]]...
      subst.
      assert (uniq E) by (eapply env_well_typed_uniq; eauto).
      unshelve epose proof (loc_transform_cse_bound_fvar _ _ _ _ BindsL) as LocTransFvar...
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans LocTransFvar); subst...
      destruct (proj2 (env_typing_inversion _ _ _ R _ _ EnvTyp BindsL))...
  - epose proof (loc_transform_cse_result Q1 E) as [Q1' LocTransQ1].
    epose proof (loc_transform_cse_result Q2 E) as [Q2' LocTransQ2].
    epose proof (loc_transform_cse_join _ _ _ _ _ LocTransQ1 LocTransQ2) as LocTransJoin.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTrans LocTransJoin); subst.
    constructor.
    eapply IHWfCse1...
    eapply IHWfCse2...
Qed.

Lemma subcapt_under_loc_transform_strong : forall Γ Δ Δ' E S C1 C2 C1' C2',
  env_well_typed S E Γ ->
  subcapt (Δ ++ Γ) S C1 C2 ->
  loc_transform_cse E C1 C1' ->
  loc_transform_cse E C2 C2' ->
  loc_transform_ctx E Δ Δ' ->
  subcapt Δ' S C1' C2'.
Proof with eauto using loc_transform_cse_wf, loc_transform_ctx_wf, subcapt_reflexivity.
  intros * EnvTyp Subcapt LocTransC1 LocTransC2 LocTransCtx.
  assert (Uniq : uniq (Δ ++ Γ)) by eauto.
  assert (WfΓ : wf_ctx Γ S) by (eapply env_well_typed_ctx_wf; eauto).
  assert (UniqE: uniq E) by (eapply env_well_typed_uniq; eauto).
  assert (WfS : wf_store_ctx S) by (eapply env_well_typed_store_ctx_wf; eauto).
  generalize dependent C1'.
  generalize dependent C2'.
  generalize dependent E.
  generalize dependent Δ'.
  dependent induction Subcapt; intros.
  - loc_transform_cse_ident_eq LocTransC2...
  - loc_transform_cse_ident_eq LocTransC1...
  - inversion H0; subst.
    rename select (binds _ _ _) into Binds.
    analyze_binds_uniq Binds; subst.
    + erewrite <- env_well_typed_preserves_dom in H1...
      epose proof (loc_transform_cse_unbound_fvar _ _ H1) as Ident.
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC1 Ident); subst...
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC2 Ident); subst...
    + epose proof (bind_typ_capt _ _ _ _ WfΓ BindsTac) as [C [R Eq]]; subst.
      unshelve epose proof (runtime_ctx_binds_loc Γ _ _ _ _ R) as [l [BindsL EqL]]...
      subst.
      unshelve epose proof (loc_transform_cse_bound_fvar _ _ _ UniqE BindsL) as LocTransFvar...
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC1 LocTransFvar); subst...
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC2 LocTransFvar); subst...
  - loc_transform_cse_ident_eq LocTransC1...
    loc_transform_cse_ident_eq LocTransC2...
  - analyze_binds_uniq H; subst.
    + rewrite <- (env_well_typed_preserves_dom _ _ _ EnvTyp) in H0.
      epose proof (loc_transform_cse_unbound_fvar _ _ H0) as Ident.
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC1 Ident); subst.
      epose proof (loc_transform_result (R # T) E) as [R' LocTransR'].
      epose proof (loc_transform_capt _ _ _ _ LocTransR') as [C0 [R0 [Eq [LocTransR LocTransT]]]]; subst.
      epose proof (loc_transform_ctx_binds_typ _ _ _ _ _ _ H0 LocTransCtx BindsTac LocTransR')...
    + unshelve epose proof (runtime_ctx_binds_loc Γ _ _ _ R T) as [l [BindsL EqL]]...
      subst.
      unshelve epose proof (loc_transform_cse_bound_fvar _ _ _ UniqE BindsL) as LocTransFvar.
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC1 LocTransFvar); subst.
      eapply IHSubcapt...
      apply loc_transform_cse_ident...
  - loc_transform_cse_ident_eq LocTransC1...
    apply subcapt_transitivity with (Q := R).
    + assert (WfΔ' : wf_ctx Δ' S) by (eapply loc_transform_ctx_wf; eauto).
      epose proof (wf_typ_from_wf_store_ctx Δ' _ _ _ _ WfS H WfΔ') as Wf.
      inversion Wf; subst.
      econstructor...
    + epose proof (loc_transform_cse_result R E) as [R' LocTransR].
      epose proof (wf_typ_from_wf_store_ctx_nil _ _ _ _ WfS H) as WfTyp.
      inversion WfTyp; subst.
      loc_transform_cse_ident_eq LocTransR. {
        intros. intro.
        epose proof (wf_cse_fvars_from_ctx _ _ _ _ H2 H0)...
        simpl in *. fsetdec.
      }
      eapply IHSubcapt...
  - epose proof (loc_transform_cse_result R1 E) as [R1' LocTransR1].
    epose proof (loc_transform_cse_result R2 E) as [R2' LocTransR2].
    epose proof (loc_transform_cse_join _ _ _ _ _ LocTransR1 LocTransR2) as LocTransJoin.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC2 LocTransJoin); subst.
    apply subcapt_join_inl...
  - epose proof (loc_transform_cse_result R1 E) as [R1' LocTransR1].
    epose proof (loc_transform_cse_result R2 E) as [R2' LocTransR2].
    epose proof (loc_transform_cse_join _ _ _ _ _ LocTransR1 LocTransR2) as LocTransJoin.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC2 LocTransJoin); subst.
    apply subcapt_join_inr...
  - epose proof (loc_transform_cse_result R1 E) as [R1' LocTransR1].
    epose proof (loc_transform_cse_result R2 E) as [R2' LocTransR2].
    epose proof (loc_transform_cse_join _ _ _ _ _ LocTransR1 LocTransR2) as LocTransJoin.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC1 LocTransJoin); subst.
    apply subcapt_join_elim...
Qed.

Lemma loc_transform_ctx_nil : forall E,
  loc_transform_ctx E nil nil.
Proof with eauto.
  intros.
  induction E...
  destruct a as [x l]...
Qed.

Lemma subcapt_under_loc_transform : forall Γ E S C1 C2 C1' C2',
  env_well_typed S E Γ ->
  loc_transform_cse E C1 C1' ->
  loc_transform_cse E C2 C2' ->
  subcapt Γ S C1 C2 ->
  subcapt nil S C1' C2'.
Proof with eauto using subcapt_under_loc_transform_strong.
  intros * EnvTyp LocTransC1 LocTransC2 Subcapt.
  rewrite_env (nil ++ Γ) in Subcapt.
  apply (subcapt_under_loc_transform_strong _ _ _ _ _ _ _ _ _ EnvTyp Subcapt LocTransC1 LocTransC2).
  apply loc_transform_ctx_nil.
Qed.

Lemma loc_transform_fun : forall E C1 R1 T1 U,
  loc_transform E (∀ (C1 # R1) T1) U ->
  exists C2 R2 T2,
    loc_transform_cse E C1 C2 /\
    loc_transform E R1 R2 /\
    loc_transform E T1 T2 /\
    U = ∀ (C2 # R2) T2.
Proof with eauto.
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
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists R1, T1; split...
  - destruct (IHLocTrans _ _ eq_refl) as [R2 [T2 [LocTransR [LocTransT Eq]]]]; subst.
    exists R2, T2; split...
Qed.

Lemma loc_transform_box : forall E T1 U,
  loc_transform E (typ_box T1) U ->
  exists T2, loc_transform E T1 T2 /\ U = typ_box T2.
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists T1; split... 
  - destruct (IHLocTrans _ eq_refl) as [T2 [LocTransT2 Eq]]; subst.
    exists T2; split...
Qed.

Lemma loc_transform_ctx_cons_typ : forall E Δ Δ' x T T',
  loc_transform_ctx E Δ Δ' ->
  loc_transform E T T' ->
  loc_transform_ctx E ((x, bind_typ T) :: Δ) ((x, bind_typ T') :: Δ').
Proof with eauto using loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub.
  intros * LocTransCtx LocTrans.
  generalize dependent T'.
  generalize dependent T.
  dependent induction LocTransCtx; intros; subst; simpl in *.
  - inversion LocTrans; subst.
    constructor...
  - inversion LocTrans; subst.
    constructor...
    simpl.
    apply IHLocTransCtx...
Qed.

Lemma loc_transform_ctx_cons_sub : forall E Δ Δ' x T T',
  loc_transform_ctx E Δ Δ' ->
  loc_transform E T T' ->
  loc_transform_ctx E ((x, bind_sub T) :: Δ) ((x, bind_sub T') :: Δ').
Proof with eauto using loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub.
  intros * LocTransCtx LocTrans.
  generalize dependent T'.
  generalize dependent T.
  dependent induction LocTransCtx; intros; subst; simpl in *.
  - inversion LocTrans; subst.
    constructor...
  - inversion LocTrans; subst.
    constructor...
    simpl.
    apply IHLocTransCtx...
Qed.

Lemma loc_transform_open_ct_fresh : forall x E T1 T2,
  x `notin`A dom E ->
  loc_transform E T1 T2 ->
  loc_transform E (open_ct T1 (cse_fvar x)) (open_ct T2 (cse_fvar x)).
Proof with eauto using loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub.
  intros * NotIn LocTrans.
  generalize dependent x.
  dependent induction LocTrans; intros; subst; simpl in *.
  - constructor...
  - destruct (x == x0); try fsetdec...
    constructor...
    unfold open_ct.
    rewrite subst_ct_open_ct_rec...
Qed.

Lemma loc_transform_open_tt_fresh : forall (X : atom) E T1 T2,
  X `notin`A dom E ->
  loc_transform E T1 T2 ->
  loc_transform E (open_tt T1 X) (open_tt T2 X).
Proof with eauto using loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub.
  intros * NotIn LocTrans.
  generalize dependent X.
  dependent induction LocTrans; intros; subst; simpl in *.
  - constructor...
  - destruct (X == x); try fsetdec...
    constructor...
    unfold open_tt.
    rewrite subst_ct_open_tt_rec...
Qed.

Lemma loc_transform_open_ct : forall Γ S E C1 C2 T1 T2,
  env_well_typed S E Γ ->
  loc_transform E T1 T2 ->
  loc_transform_cse E C1 C2 ->
  loc_transform E (open_ct T1 C1) (open_ct T2 C2).
Proof with eauto using loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub.
  intros * EnvTyp LocTransT1 LocTransC1.
  generalize dependent S.
  generalize dependent Γ.
  generalize dependent C1.
  generalize dependent C2.
  dependent induction LocTransT1; intros; subst; simpl in *.
  { inversion LocTransC1; subst... }
  inversion LocTransC1; inversion EnvTyp; subst.
  constructor...
  unfold open_ct. rewrite subst_ct_open_rec...
Qed.

Lemma loc_transform_open_ct_bound_var : forall Γ S E T1 T2 x l,
  env_well_typed S E Γ ->
  loc_transform E T1 T2 ->
  binds x l E ->
  loc_transform E (open_ct T1 (cse_fvar x)) (open_ct T2 (cse_loc l)).
Proof with eauto.
  intros.
  eapply loc_transform_open_ct...
  eapply loc_transform_cse_bound_fvar...
Qed.

Lemma loc_transform_wf : forall Γ Δ Δ' E S T1 T2,
  env_well_typed S E Γ ->
  wf_ctx (Δ ++ Γ) S ->
  wf_typ (Δ ++ Γ) S T1 ->
  loc_transform E T1 T2 ->
  loc_transform_ctx E Δ Δ' ->
  wf_typ Δ' S T2.
Proof with eauto using loc_transform_ctx_wf, loc_transform_cse_wf, loc_transform_ctx_binds_sub, loc_transform_pure.
  intros * EnvTyp WfCtx WfTyp LocTrans LocTransCtx.
  assert (WfΓ : wf_ctx Γ S) by (eapply env_well_typed_ctx_wf; eauto).
  generalize dependent T2.
  generalize dependent Δ'.
  generalize dependent E.
  dependent induction WfTyp; intros; subst; simpl in *.
  - analyze_binds_uniq H...
    + erewrite <- env_well_typed_preserves_dom in H0...
      epose proof (loc_transform_unbound_var _ _ H0).
      epose proof (loc_transform_deterministic _ _ _ _ LocTrans H); subst...
      epose proof (loc_transform_result T E) as [T' LocTransT']...
    + exfalso.
      epose proof (runtime_ctx_no_type_bindings _ _ _ EnvTyp) as NoTypeBinds.
      unfold no_type_bindings in NoTypeBinds.
      specialize (NoTypeBinds X T)...
  - loc_transform_ident_eq LocTrans...
  - epose proof (loc_transform_fun _ _ _ _ _ LocTrans) as [C' [R' [T' [LocTransC [LocTransR [LocTransT Eq]]]]]]; subst.
    pick fresh x and apply wf_typ_arr.
    eapply IHWfTyp...
    apply loc_transform_equiv...
    eapply (H0 x ltac:(fsetdec) Γ ((x, bind_typ (C # R)) :: Δ)) with (E := E); auto.
    + constructor...
    + apply loc_transform_ctx_cons_typ...
      eapply loc_transform_equiv...
    + eapply loc_transform_open_ct_fresh...
      erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp).
      fsetdec.
  - epose proof (loc_transform_tfun _ _ _ _ LocTrans) as [R' [T' [LocTransR [LocTransT Eq]]]]; subst.
    pick fresh x and apply wf_typ_all.
    eapply IHWfTyp...
    eapply loc_transform_pure...
    eapply (H1 x ltac:(fsetdec) Γ ((x, bind_sub R) :: Δ)) with (E := E); auto.
    + constructor...
    + apply loc_transform_ctx_cons_sub...
    + eapply loc_transform_open_tt_fresh...
      erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp).
      fsetdec.
  - epose proof (loc_transform_box _ _ _ LocTrans) as [T' [LocTransT' Eq]]; subst.
    constructor...
  - eapply loc_transform_capt in LocTrans as [C' [R' [Eq [LocTransC LocTransR]]]]; subst.
    constructor...
Qed.

Lemma loc_transform_wf_nil : forall E Γ S T1 T2,
  env_well_typed S E Γ ->
  wf_typ Γ S T1 ->
  loc_transform E T1 T2 ->
  wf_typ nil S T2.
Admitted.
(* TODO for Sam *)

Lemma sub_under_loc_transform_strong : forall Γ Δ Δ' E S T1 T2 T1' T2',
  env_well_typed S E Γ ->
  sub (Δ ++ Γ) S T1 T2 ->
  loc_transform E T1 T1' ->
  loc_transform E T2 T2' ->
  loc_transform_ctx E Δ Δ' ->
  sub Δ' S T1' T2'.
Proof with eauto using subcapt_under_loc_transform_strong, loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub, sub_reflexivity, loc_transform_ctx_wf, loc_transform_pure, loc_transform_wf.
  intros * EnvTyp Sub LocTransC1 LocTransC2 LocTransCtx.
  assert (Uniq : uniq (Δ ++ Γ)) by eauto.
  assert (WfΓ : wf_ctx Γ S) by (eapply env_well_typed_ctx_wf; eauto).
  assert (UniqE: uniq E) by (eapply env_well_typed_uniq; eauto).
  assert (WfS : wf_store_ctx S) by (eapply env_well_typed_store_ctx_wf; eauto).
  generalize dependent T1'.
  generalize dependent T2'.
  generalize dependent E.
  generalize dependent Δ'.
  dependent induction Sub; intros.
  - inversion H0; subst.
    rename select (binds _ _ _) into Binds.
    analyze_binds_uniq Binds; subst.
    + erewrite <- env_well_typed_preserves_dom in H1...
      epose proof (loc_transform_unbound_var _ _ H1).
      epose proof (loc_transform_deterministic _ _ _ _ LocTransC1 H2); subst...
      epose proof (loc_transform_deterministic _ _ _ _ LocTransC2 H2); subst...
    + exfalso.
      epose proof (runtime_ctx_no_type_bindings _ _ _ EnvTyp) as NoTypeBinds.
      unfold no_type_bindings in NoTypeBinds.
      specialize (NoTypeBinds X T)...
  - rename select (binds _ _ _) into Binds.
    analyze_binds_uniq Binds; subst.
    + erewrite <- (env_well_typed_preserves_dom _ _ _ EnvTyp) in H.
      epose proof (loc_transform_unbound_var _ _ H).
      epose proof (loc_transform_deterministic _ _ _ _ LocTransC1 H0); subst.
      epose proof (loc_transform_result U E) as [U' LocTransU]...
    + exfalso.
      epose proof (runtime_ctx_no_type_bindings _ _ _ EnvTyp) as NoTypeBinds.
      unfold no_type_bindings in NoTypeBinds.
      specialize (NoTypeBinds X U)...
  - epose proof (loc_transform_capt _ _ _ _ LocTransC1) as [C1' [R1' [Eq1 [LocTransC1' LocTransR1']]]]; subst.
    epose proof (loc_transform_capt _ _ _ _ LocTransC2) as [C2' [R2' [Eq2 [LocTransC2' LocTransR2']]]]; subst.
    destruct ((proj1 (loc_transform_equiv _ _ _ _ _)) LocTransC1).
    destruct ((proj1 (loc_transform_equiv _ _ _ _ _)) LocTransC2).
    constructor...
  - loc_transform_ident_eq LocTransC2...
  - epose proof (loc_transform_fun _ _ _ _ _ LocTransC1) as [C1r [R1r [T1r [LocTransC1r [LocTransR1r [LocTransT1 Eq]]]]]]; subst.
    epose proof (loc_transform_fun _ _ _ _ _ LocTransC2) as [C2r [R2r [T2r [LocTransC2r [LocTransR2r [LocTransT2 Eq']]]]]]; subst.
    pick fresh x and apply sub_arr.
    + eapply IHSub...
    + eapply loc_transform_pure...
    + eapply loc_transform_pure...
    + eapply subcapt_under_loc_transform_strong...
    + eapply (H3 x ltac:(fsetdec) Γ ((x, bind_typ (C2 # R2)) :: Δ)) with (E := E); auto.
      * constructor...
      * apply loc_transform_ctx_cons_typ...
        eapply loc_transform_equiv...
      * eapply loc_transform_open_ct_fresh...
        erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp).
        fsetdec.
      * eapply loc_transform_open_ct_fresh...
        erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp).
        fsetdec.
  - epose proof (loc_transform_tfun _ _ _ _ LocTransC1) as [R1r [T1r [LocTransR1 [LocTransT1 Eq]]]]; subst.
    epose proof (loc_transform_tfun _ _ _ _ LocTransC2) as [R2r [T2r [LocTransR2 [LocTransT2 Eq']]]]; subst.
    pick fresh x and apply sub_all.
    + eapply IHSub...
    + eapply loc_transform_pure...
    + eapply loc_transform_pure...
    + eapply (H2 x ltac:(fsetdec) Γ ((x, bind_sub R2) :: Δ)) with (E := E); auto.
      * constructor...
      * apply loc_transform_ctx_cons_sub...
      * eapply loc_transform_open_tt_fresh...
        erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp).
        fsetdec.
      * eapply loc_transform_open_tt_fresh...
        erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp).
        fsetdec.
  - epose proof (loc_transform_box _ _ _ LocTransC1) as [T1r [LocTransT1 Eq]]; subst.
    epose proof (loc_transform_box _ _ _ LocTransC2) as [T2r [LocTransT2 Eq']]; subst.
    constructor...
Qed.

Lemma sub_under_loc_transform : forall Γ E S T1 T2 T1' T2',
  env_well_typed S E Γ ->
  loc_transform E T1 T1' ->
  loc_transform E T2 T2' ->
  sub Γ S T1 T2 ->
  sub nil S T1' T2'.
Admitted.
(* TODO for Sam *)

Lemma loc_transform_exp_abs : forall E e e2 C R,
  loc_transform_exp E (λ ((C # R)) e) e2 ->
  exists C' R' e',
    loc_transform_cse E C C' /\
    loc_transform E R R' /\
    loc_transform_exp E e e' /\
    e2 = (λ ((C' # R')) e').
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists C, R, e; repeat split...
  - destruct (IHLocTrans _ _ _ eq_refl) as [C' [R' [e' [LocTransC [LocTransR [LocTransExp Eq]]]]]]; subst.
    exists C', R', e'; repeat split...
Qed.

Lemma loc_transform_exp_tabs : forall E T e e2,
  loc_transform_exp E (Λ [T] e) e2 ->
  exists T' e',
    loc_transform E T T' /\
    loc_transform_exp E e e' /\
    e2 = (Λ [T'] e').
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists T, e; split...
  - destruct (IHLocTrans _ _ eq_refl) as [T' [e' [LocTransT [LocTransExp Eq]]]]; subst.
    exists T', e'; split...
Qed.

Lemma loc_transform_exp_app : forall E f x e,
  loc_transform_exp E (f @ x) e ->
  exists (f' x' : var_like),
    loc_transform_exp E f f' /\
    loc_transform_exp E x x' /\
    e = (f' @ x').
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists f, x; repeat split...
  - destruct (IHLocTrans _ _ eq_refl) as [f' [x' [LocTransF [LocTransX Eq]]]]; subst.
    exists f', x'; repeat split...
Qed.

Lemma loc_transform_exp_tapp : forall E e T e2,
  loc_transform_exp E (e @ [T]) e2 ->
  exists T' (e' : var_like),
    loc_transform E T T' /\
    loc_transform_exp E e e' /\
    e2 = (e' @ [T']).
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists T, e; split...
  - destruct (IHLocTrans _ _ eq_refl) as [T' [e' [LocTransT [LocTransExp Eq]]]]; subst.
    exists T', e'; split...
Qed.

Lemma loc_transform_exp_let : forall E k e e2,
  loc_transform_exp E (let= e in k) e2 ->
  exists e' k',
    loc_transform_exp E k k' /\
    loc_transform_exp E e e' /\
    e2 = (let= e' in k').
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists e, k; repeat split...
  - destruct (IHLocTrans _ _ eq_refl) as [e' [k' [LocTransE [LocTransK Eq]]]]; subst.
    exists e', k'; repeat split...
Qed.

Lemma loc_transform_exp_box : forall E e e2,
  loc_transform_exp E (box e) e2 ->
  exists (e' : var_like),
    loc_transform_exp E e e' /\
    e2 = box e'.
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists e; split...
  - destruct (IHLocTrans _ eq_refl) as [e' [LocTransE Eq]]; subst.
    exists e'; split...
Qed.

Lemma loc_transform_exp_unbox : forall E C x e2,
  loc_transform_exp E (C ⟜ x) e2 ->
  exists C' (x' : var_like),
    loc_transform_cse E C C' /\
    loc_transform_exp E x x' /\
    e2 = (C' ⟜ x').
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists C, x; repeat split...
  - destruct (IHLocTrans _ _ eq_refl) as [C' [x' [LocTransC [LocTransX Eq]]]]; subst.
    exists C', x'; repeat split...
Qed.

Lemma loc_transform_cse_exp_cv : forall E e1 e2,
  loc_transform_exp E e1 e2 ->
  loc_transform_cse E (exp_cv e1) (exp_cv e2).
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - constructor...
  - rewrite <- subst_cse_loc_cv_commutes_with_subst_ve in IHLocTrans...
Qed.


Lemma loc_transform_exp_open_ve_unbound_var : forall E e1 e2 x,
  x `notin`A dom E ->
  loc_transform_exp E e1 e2 ->
  loc_transform_exp E (open_ve e1 x (cse_fvar x)) (open_ve e2 x (cse_fvar x)).
Proof with eauto.
  intros * NotIn LocTrans.
  generalize dependent x.
  dependent induction LocTrans; intros; subst; simpl in *.
  - constructor...
  - destruct (x == x0); try fsetdec...
    constructor...
    unfold open_ve in *.
    rewrite subst_ve_open_ve_rec...
    simpl...
    destruct (x == x0); try fsetdec...
Qed.

Lemma loc_transform_exp_open_te_unbound_var : forall E e1 e2 X,
  X `notin`A dom E ->
  loc_transform_exp E e1 e2 ->
  loc_transform_exp E (open_te e1 X) (open_te e2 X).
Proof with eauto.
  intros * NotIn LocTrans.
  generalize dependent X.
  dependent induction LocTrans; intros; subst; simpl in *.
  - constructor...
  - destruct (X == x); try fsetdec...
    constructor...
    unfold open_te in *.
    replace (open_te_rec 0 X e1) with (open_te e1 X) by reflexivity.
    rewrite <- subst_ve_open_te_var...
Qed.

Lemma loc_transform_open_tt : forall E T T' P P',
  loc_transform E T T' ->
  loc_transform E P P' ->
  loc_transform E (open_tt T P) (open_tt T' P').
Proof with eauto using loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub.
  intros * LocTransT LocTransP.
  generalize dependent P.
  generalize dependent P'.
  dependent induction LocTransT; intros; subst; simpl in *.
  - inversion LocTransP; subst.
    constructor...
  - inversion LocTransP; subst.
    constructor...
    unfold open_tt.
    rewrite subst_ct_open_tt_rec...
Qed.

Lemma loc_transform_exp_fvar_like : forall E (v v' : var_like),
  fvar_like v ->
  loc_transform_exp E v v' ->
  fvar_like v'.
Proof with eauto.
  intros * FvarLike LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *...
Qed.

Lemma typing_under_loc_transform_strong : forall Γ Δ Δ' E S e e' T T',
  env_well_typed S E Γ ->
  typing (Δ ++ Γ) S e T ->
  loc_transform E T T' ->
  loc_transform_exp E e e' ->
  loc_transform_ctx E Δ Δ' ->
  typing Δ' S e' T'.
Proof with eauto using loc_transform_ctx_binds_typ, loc_transform_ctx_binds_sub, loc_transform_cse_wf, loc_transform_wf, loc_transform_pure, wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil, loc_transform_ctx_wf, loc_transform_exp_fvar_like.
  intros * EnvTyp Typ LocTrans LocTransExp LocTransCtx.
  assert (WfCtx : wf_ctx (Δ ++ Γ) S) by applys typing_regular Typ.
  assert (WfΓ : wf_ctx Γ S) by (eapply env_well_typed_ctx_wf; eauto).
  assert (Uniq : uniq (Δ ++ Γ)) by eauto.
  generalize dependent T'.
  generalize dependent e'.
  generalize dependent E.
  generalize dependent Δ'.
  dependent induction Typ; intros; subst; simpl in *.
  - Case "typing_var".
    simpl_env in H0.
    analyze_binds_uniq H0; subst.
    + erewrite <- env_well_typed_preserves_dom in H1...
      epose proof (loc_transform_exp_unbound_var _ _ H1) as Ident.
      epose proof (loc_transform_exp_deterministic _ _ _ _ LocTransExp Ident); subst.
      epose proof (loc_transform_capt _ _ _ _ LocTrans) as [C' [R' [Eq [LocTransC LocTransR]]]]; subst.
      epose proof (loc_transform_cse_unbound_fvar E x H1) as IdentFvar.
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC IdentFvar); subst.
      epose proof (loc_transform_cse_result C E) as [C' LocTransC'].
      unshelve epose proof (loc_transform_ctx_binds_typ _ _ _ _ _ (C' # R') H1 LocTransCtx BindsTac _).
      apply loc_transform_equiv...
      econstructor...
    + epose proof (runtime_ctx_binds_loc _ _ _ _ _ _ EnvTyp BindsTac) as [l [BindsL EqL]]; subst.
      unshelve epose proof (loc_transfrom_exp_bound_fvar _ _ _ _ BindsL)...
      epose proof (loc_transform_exp_deterministic _ _ _ _ LocTransExp H0); subst.
      epose proof (loc_transform_capt _ _ _ _ LocTrans) as [C' [R' [Eq [LocTransC LocTransR]]]]; subst.
      unshelve epose proof (loc_transform_cse_bound_fvar _ _ _ _ BindsL) as LocTransFvar...
      epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC LocTransFvar); subst.
      epose proof ((proj2 (env_typing_inversion _ _ _ R _ _ EnvTyp BindsL)) BindsTac) as [C StoreBinds]...
      loc_transform_ident_eq LocTransR.
      enough (wf_typ nil S (C # R)).
      inversion H2; subst...
      eapply wf_typ_from_wf_store_ctx_nil...
      econstructor...
  - Case "typing_loc".
    loc_transform_exp_ident_eq LocTransExp...
    epose proof (loc_transform_capt _ _ _ _ LocTrans) as [C' [R' [Eq [LocTransC LocTransR]]]]; subst.
    loc_transform_cse_ident_eq LocTransC...
    loc_transform_ident_eq LocTransR.
    enough (wf_typ nil S (C # R)).
    inversion H1; subst...
    eapply wf_typ_from_wf_store_ctx_nil...
    econstructor...
  - Case "typing_abs".
    epose proof (loc_transform_exp_abs _ _ _ _ _ LocTransExp) as [C0 [R0 [e0 [LocTransC [LocTransR [LocTransE Eq]]]]]]; subst.
    epose proof (loc_transform_capt _ _ _ _ LocTrans) as [C' [Fun' [Eq' [LocTransC' LocTransFun']]]]; subst.
    epose proof (loc_transform_cse_exp_cv _ _ _ LocTransE).
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC' H2) as EqC; subst.
    epose proof (loc_transform_fun _ _ _ _ _ LocTransFun') as [C2 [R2 [T2 [LocTransC2 [LocTransR2 [LocTransT2 Eq]]]]]]; subst.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC2 LocTransC) as EqC2; subst.
    epose proof (loc_transform_deterministic _ _ _ _ LocTransR2 LocTransR) as EqR; subst.
    pick fresh x and apply typing_abs.
    unshelve epose proof (loc_transform_wf _ _ _ _ _ _ (C0 # R0) EnvTyp WfCtx H _ LocTransCtx)...
    apply loc_transform_equiv...
    eapply (H1 x ltac:(fsetdec) Γ ((x, bind_typ (C # R)) :: Δ)); auto.
    + constructor...
    + constructor...
    + apply EnvTyp.
    + eapply loc_transform_ctx_cons_typ...
      apply loc_transform_equiv...
    + eapply loc_transform_exp_open_ve_unbound_var...
      erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp)...
    + eapply loc_transform_open_ct...
      eapply loc_transform_cse_unbound_fvar...
      erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp)...
  - Case "typing_app".
    epose proof (loc_transform_exp_app _ _ _ _ LocTransExp) as [f' [x' [LocTransF [LocTransX Eq]]]]; subst.
    epose proof (loc_transform_result T E) as [T2 LocTransT2].
    replace (var_cv x) with (exp_cv x) in LocTrans by reflexivity.
    epose proof (loc_transform_cse_exp_cv _ _ _ LocTransX).
    epose proof (loc_transform_open_ct _ _ _ _ _ _ _ EnvTyp LocTransT2 H1).
    epose proof (loc_transform_deterministic _ _ _ _ LocTrans H2) as EqF; subst.
    epose proof (loc_transform_cse_result C E) as [C' LocTransC].
    epose proof (loc_transform_result (∀ ((D # Q)) T) E) as [Fun' LocTransFun].
    epose proof (loc_transform_fun _ _ _ _ _ LocTransFun) as [D' [Q' [T' [LocTransD' [LocTransQ' [LocTransT Eq]]]]]]; subst.
    epose proof (loc_transform_deterministic _ _ _ _ LocTransT2 LocTransT) as EqT; subst.
    eapply typing_app.
    + eapply (loc_transform_exp_fvar_like E f)...
    + eapply (loc_transform_exp_fvar_like E x)...
    + eapply IHTyp1...
      apply loc_transform_equiv; split...
    + eapply IHTyp2...
      apply loc_transform_equiv; split...
  - Case "typing_let".
    epose proof (loc_transform_exp_let _ _ _ _ LocTransExp) as [e2 [k2 [LocTransE [LocTransK Eq]]]]; subst.
    epose proof (loc_transform_cse_result C1 E) as [C1' LocTransC1].
    epose proof (loc_transform_result R1 E) as [R1' LocTransR1].
    pick fresh x and apply typing_let.
    + eapply IHTyp...
      apply loc_transform_equiv; split...
    + eapply (H0 x ltac:(fsetdec) Γ ((x, bind_typ (C1 # R1)) :: Δ)) with (E := E); auto.
      * constructor...
      * constructor...
      * eapply loc_transform_ctx_cons_typ...
        apply loc_transform_equiv...
      * eapply loc_transform_exp_open_ve_unbound_var...
        erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp)...
  - Case "typing_tabs".
    epose proof (loc_transform_exp_tabs _ _ _ _ LocTransExp) as [V2 [e2 [LocTransV2 [LocTransE Eq]]]]; subst.
    epose proof (loc_transform_capt _ _ _ _ LocTrans) as [C' [Tfun' [Eq' [LocTransC' LocTransFun']]]]; subst.
    epose proof (loc_transform_cse_exp_cv _ _ _ LocTransE).
    epose proof (loc_transform_tfun _ _ _ _ LocTransFun') as [R' [T1' [LocTransR [LocTransT1 Eq]]]]; subst.
    epose proof (loc_transform_deterministic _ _ _ _ LocTransV2 LocTransR) as EqV2; subst.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC' H3) as EqC; subst.
    pick fresh x and apply typing_tabs.
    + eapply loc_transform_wf...
    + eapply loc_transform_pure...
    + eapply (H2 x ltac:(fsetdec) Γ ((x, bind_sub V) :: Δ)) with (E := E); auto; try constructor...
      * apply loc_transform_ctx_cons_sub...
      * apply loc_transform_exp_open_te_unbound_var...
        erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp)...
      * eapply loc_transform_open_tt_fresh...
        erewrite (env_well_typed_preserves_dom _ _ _ EnvTyp).
        fsetdec.
  - Case "typing_tapp".
    epose proof (loc_transform_exp_tapp _ _ _ _ LocTransExp) as [P' [x' [LocTransP [LocTransX Eq]]]]; subst.
    epose proof (loc_transform_result T E) as [T2 LocTransT2].
    epose proof (loc_transform_open_tt _ _ _ _  _ LocTransT2 LocTransP).
    epose proof (loc_transform_deterministic _ _ _ _ LocTrans H1); subst.
    epose proof (loc_transform_cse_result C E) as [C' LocTransC].
    epose proof (loc_transform_result (∀ [Q] T) E) as [Fun' LocTransFun].
    epose proof (loc_transform_tfun _ _ _ _  LocTransFun) as [Q' [T' [LocTransQ [LocTransT Eq]]]]; subst.
    epose proof (loc_transform_deterministic _ _ _ _ LocTransT2 LocTransT) as EqT; subst.
    eapply typing_tapp.
    + eapply (loc_transform_exp_fvar_like E x)...
    + eapply IHTyp...
      apply loc_transform_equiv; split...
    + eapply sub_under_loc_transform_strong with (Δ := Δ) (Δ' := Δ')...
  - Case "typing_box".
    epose proof (loc_transform_exp_box _ _ _ LocTransExp) as [e2 [LocTransE Eq]]; subst.
    epose proof (loc_transform_capt _ _ _ _ LocTrans) as [C' [R' [Eq' [LocTransBot LocTransBox]]]]; subst.
    loc_transform_cse_ident_eq LocTransBot.
    { intros; fsetdec. }
    epose proof (loc_transform_box _ _ _ LocTransBox) as [T2' [LocTransT2' EqT]]; subst.
    epose proof (loc_transform_capt _ _ _ _ LocTransT2') as [C' [R' [Eq' [LocTransC' LocTransR']]]]; subst.
    eapply typing_box...
  - Case "typing_unbox".
    epose proof (loc_transform_exp_unbox _ _ _ _ LocTransExp) as [C' [x' [LocTransC [LocTransX Eq]]]]; subst.
    epose proof (loc_transform_capt _ _ _ _ LocTrans) as [C'' [R' [Eq' [LocTransC' LocTransR]]]]; subst.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC' LocTransC) as EqC; subst.
    assert (loc_transform E (C # R) (C' # R')) by (eapply loc_transform_equiv; split; eauto).
    epose proof (loc_transform_result ((□ C # R)) E) as [Box LocTransBox].
    epose proof (loc_transform_box _ _ _ LocTransBox) as [T2' [LocTransT2' EqT]]; subst.
    epose proof (loc_transform_capt _ _ _ _ LocTransT2') as [C'' [R'' [Eq'' [LocTransC'' LocTransR'']]]]; subst.
    epose proof (loc_transform_cse_deterministic _ _ _ _ LocTransC'' LocTransC') as EqC2; subst.
    epose proof (loc_transform_deterministic _ _ _ _ LocTransR'' LocTransR) as EqR; subst.
    eapply typing_unbox.
    * eapply (loc_transform_exp_fvar_like E x)...
    * eapply IHTyp...
      eapply loc_transform_equiv; split...
      apply loc_transform_cse_ident...
    * eapply loc_transform_cse_wf with (Δ := Δ) (Δ' := Δ')...
  - Case "typing_sub".
    epose proof (loc_transform_result R E) as [R' LocTransR'].
    eapply typing_sub with (R := R')...
    eapply sub_under_loc_transform_strong with (Δ := Δ) (Δ' := Δ')...
Qed.

Lemma typing_under_loc_transform : forall Γ E S e e' T T',
  env_well_typed S E Γ ->
  typing Γ S e T ->
  loc_transform E T T' ->
  loc_transform_exp E e e' ->
  typing nil S e' T'.
Proof with eauto using wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil.
  intros * EnvTyp Typ LocTrans LocTransExp.
  eapply typing_under_loc_transform_strong with (Δ := nil) (Δ' := nil)...
  apply loc_transform_ctx_nil.
Qed.

Lemma frame_typing_implies_typing : forall E S e e' T,
  frame_typing S (e, E) T ->
  loc_transform_exp E e e' ->
  typing nil S e' T.
Proof with eauto using sub_reflexivity.
  intros * FrameTyp LocTransExp.
  generalize dependent e'.
  dependent induction FrameTyp; intros; subst; simpl in *.
  - eapply typing_under_loc_transform...
  - eapply typing_sub...
Qed.

Lemma subst_ct_invert_fun : forall T U1 U2 D x,
  subst_ct x D T = ∀ (U1) U2 ->
  exists U1' U2',
    T = ∀ (U1') U2' /\ U1 = subst_ct x D U1' /\ U2 = subst_ct x D U2'.
Proof with eauto.
  intros * Eq.
  generalize dependent U1.
  generalize dependent U2.
  induction T; simpl in *; intros; try inversion Eq...
  - destruct v; inversion Eq; subst.
Qed.

Lemma loc_transform_fun_rev : forall E U2 T2 U,
  loc_transform E U (∀ (U2) T2) ->
  exists U1 T1,
    loc_transform E U1 U2 /\
    loc_transform E T1 T2 /\
    U = ∀ (U1) T1.
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists U2, T2; repeat split...
  - destruct (IHLocTrans _ _ eq_refl) as [U1 [T1 [LocTransU [LocTransT Eq]]]]; subst.
    epose proof (subst_ct_invert_fun _ _ _ _ _ Eq) as [U0 [T0 [EqT [EqU0 EqT0]]]]; subst.
    exists U0, T0; repeat split...
Qed.

Lemma loc_transform_capt_rev : forall E C2 R2 U,
  loc_transform E U (C2 # R2) ->
  exists C1 R1,
    loc_transform_cse E C1 C2 /\
    loc_transform E R1 R2 /\
    U = C1 # R1.
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *.
  - exists C2, R2; repeat split...
  - destruct (IHLocTrans _ _ eq_refl) as [C1 [R1 [LocTransC [LocTransR Eq]]]]; subst.
    epose proof (subst_ct_invert_capt _ _ _ _ _ Eq) as [C0 [R0 [EqC [EqR EqU]]]]; subst.
    exists C0, R0; repeat split...
Qed.

Lemma subst_cse_loc_invert_top : forall x C l,
  subst_cse x (cse_loc l) C = cse_top ->
  C = cse_top.
Proof with eauto.
  intros * Eq.
  generalize dependent l.
  induction C; simpl in *; intros; try inversion Eq; subst...
  destruct (x == a); subst...
  discriminate Eq.
Qed.

Lemma loc_transform_cse_top_rev : forall E C,
  loc_transform_cse E C cse_top ->
  C = cse_top.
Proof with eauto.
  intros * LocTrans.
  dependent induction LocTrans; intros; subst; simpl in *...
  eapply subst_cse_loc_invert_top...
Qed.
