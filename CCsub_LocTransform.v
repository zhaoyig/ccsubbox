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

Lemma loc_tranform_equiv : forall E C R C' R',
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
    apply loc_tranform_equiv...
    eapply (H0 x ltac:(fsetdec) Γ ((x, bind_typ (C # R)) :: Δ)) with (E := E); auto.
    + constructor...
    + apply loc_transform_ctx_cons_typ...
      eapply loc_tranform_equiv...
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
    destruct ((proj1 (loc_tranform_equiv _ _ _ _ _)) LocTransC1).
    destruct ((proj1 (loc_tranform_equiv _ _ _ _ _)) LocTransC2).
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
        eapply loc_tranform_equiv...
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
