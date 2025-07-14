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
Require Import CCsub_LocTransform.
(* Require Import CCsub_Precise. *)
(* Require Import CCsub_PreciseSubstitution. *)

(* Lemma open_ct_invert : forall T C R x, *)
(*   open_ct T (cse_fvar x) = C # R -> *)
(*   exists C' R', T = C' # R' /\ C = open_cse 0 (cse_fvar x) C' /\ R = open_ct R' (cse_fvar x). *)
(* Proof with eauto. *)
(*   intros * Eq. *)
(*   generalize dependent C. *)
(*   generalize dependent R. *)
(*   unfold open_ct in *. *)
(*   induction T; simpl in *... *)
(*   intros. *)
(*   exists c T... *)
(*   repeat split... *)
(* Qed. *)

(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

Lemma frame_typing_inv_app : forall S lx (f x : atom) E T,
  binds x lx E ->
  frame_typing S (f @ x, E) T ->
  exists C D Q U, frame_typing S (exp_var f, E) (C # (∀ (D # Q) U))
               /\ frame_typing S (exp_var x, E) (D # Q)
               /\ sub nil S (open_ct U (cse_loc lx)) T.
Proof with eauto.
  intros * Binds Frame.
  inversion Frame; subst.
  rename select (env_well_typed _ _ _) into EnvTyp.
  rename select (typing _ _ _ _) into Typ.
  assert (WfT : wf_typ nil S T) by applys frame_typing_regular Frame.
  destruct (typing_inv_app _ _ _ _ _ Typ) as [C9 [D [Q [U0 [xTyp [yTyp USubC1R1]]]]]].
  epose proof (loc_transform_result (∀ (D # Q) U0) E) as [TFun LocTransDQ].
  epose proof (loc_transform_fun _ _ _ _ _ LocTransDQ) as [D' [Q' [U0' [LocTransD [LocTransQ [LocTransU0 Eq'']]]]]]; subst...
  epose proof (loc_transform_cse_result C9 E) as [C9' LocTransC9].
  exists C9', D', Q', U0'.
  repeat split; try econstructor...
  - eapply (proj2 (loc_transform_equiv _ _ _ _ _))...
  - eapply (proj2 (loc_transform_equiv _ _ _ _ _))...
  - epose proof (loc_transform_open_ct_bound_var _ _ _ _ _ _ _ EnvTyp LocTransU0 Binds).
    eapply sub_under_loc_transform...
Qed.

Lemma sub_top_implies_top : forall Γ S T,
  sub Γ S typ_top T ->
  T = typ_top.
Proof with eauto.
  intros * Sub.
  inversion Sub; subst; clear Sub...
Qed.

(* TODO: might want a stronger conclusion *)
Lemma sub_inv_arr_right : forall Γ S U T C R,
  sub Γ S (∀ ((C # R)) T) U ->
  U = typ_top \/
  exists C' R' T', U = (∀ ((C' # R')) T')
                /\ sub Γ S (C' # R') (C # R).
Proof with eauto.
  intros * Sub.
  inversion Sub; subst; clear Sub.
  - left; reflexivity.
  - right; eexists...
Qed.

Lemma subst_cse_loc_invert_join : forall x l C1 C2 C,
  cse_join C1 C2 = subst_cse x (cse_loc l) C  ->
  exists C1' C2',
    C = cse_join C1' C2' /\
    C1 = subst_cse x (cse_loc l) C1' /\
    C2 = subst_cse x (cse_loc l) C2'.
Proof with eauto.
  intros * Eq.
  generalize dependent C1.
  generalize dependent C2.
  generalize dependent x.
  generalize dependent l.
  induction C; intros; simpl in *; try discriminate...
  - (* Case "cse_fvar". *)
    destruct (x == a); discriminate.
  - (* Case "cse_join". *)
    inversion Eq.
    exists C1, C2; repeat split...
Qed.

Lemma subcapt_through_subst_cse_rev_aux : forall Γ S C D R x l,
  subcapt Γ S (subst_cse x (cse_loc l) C) (subst_cse x (cse_loc l) D) ->
  wf_ctx ([(x, bind_typ (cse_loc l # R))] ++ Γ) S ->
  wf_cse ([(x, bind_typ (cse_loc l # R))] ++ Γ) S C ->
  wf_cse ([(x, bind_typ (cse_loc l # R))] ++ Γ) S D ->
  subcapt ([(x, bind_typ (cse_loc l # R))] ++ Γ) S C D.
Proof with eauto using subcapt_reflexivity, wf_cse_weaken_head.
  intros * Sub WfCtx WfC WfD.
  generalize dependent R.
  dependent induction Sub; intros;
    try rename select (_ = subst_cse _ _ D) into EqD;
    try rename select (_ = subst_cse _ _ C) into EqC...
  - (* Case "subcapt_top" *)
    enough (D = cse_top); subst...
    induction D; simpl in *; try discriminate...
    destruct (x0 == a); discriminate...
  - (* Case "subcapt_bot". *)
    enough (C = cse_bot); subst...
    induction C; simpl in *; try discriminate...
    destruct (x0 == a); discriminate...
  - (* Case "subcapt_refl_var" *)
    assert (C = cse_fvar X); subst...
    { induction C; simpl in *; try discriminate...
      destruct (x0 == a); try discriminate... }
    assert (D = cse_fvar X); subst...
    { induction D; simpl in *; try discriminate...
      destruct (x0 == a); try discriminate... }
  - (* Case "subcapt_refl_loc" *)
    assert (C = cse_loc l0 \/ (C = cse_fvar x0 /\ l0 = l)); subst...
    { induction C; simpl in *; try discriminate...
      destruct (x0 == a); try fsetdec; inversion EqC...
      right; split; f_equal... }
    assert (D = cse_loc l0 \/ (D = cse_fvar x0 /\ l0 = l)); subst...
    { induction D; simpl in *; try discriminate...
      destruct (x0 == a); try fsetdec; inversion EqD...
      right; split; f_equal... }
    destruct H1 as [Eq1 | [Eq1 LocEq1]]; destruct H2 as [Eq2 | [Eq2 LocEq2]]; subst...
    simpl in EqD...
    admit.
    Admitted.
(*   - (* Case "subcapt_trans_var" *) *)
(*     assert (WfR : wf_cse Γ S R) by applys subcapt_regular Sub. *)
(*     assert (x0 `notin`A cse_fvars R). { *)
(*       intro In. *)
(*       epose proof (wf_cse_fvars_from_ctx _ _ _ _ WfR In)... *)
(*       inversion WfCtx... *)
(*     } *)
(*     assert (C = cse_fvar X); subst. { *)
(*       induction C; simpl in *; try discriminate... *)
(*       destruct (x0 == a); inversion x... *)
(*     } *)
(*     econstructor... *)
(*     eapply IHSub... *)
(*     rewrite <- subst_cse_fresh... *)
(*   - (* Case "subcapt_trans_loc" *) *)
(*     assert (WfR : wf_cse Γ S R) by applys subcapt_regular Sub. *)
(*     assert (C = cse_loc l0 \/ (C = cse_fvar x0 /\ l0 = l)). { *)
(*       induction C; simpl in *; try discriminate... *)
(*       destruct (x0 == a); try fsetdec; inversion x... *)
(*       right; split; f_equal... *)
(*     } *)
(*     assert (x0 `notin`A cse_fvars R). { *)
(*       intro In. *)
(*       epose proof (wf_cse_fvars_from_ctx _ _ _ _ WfR In)... *)
(*       inversion WfCtx... *)
(*     } *)
(*     destruct H0 as [Eq | [Eq LocEq]]; subst... *)
(*     + econstructor... *)
(*       eapply IHSub... *)
(*       rewrite <- subst_cse_fresh... *)
(*     + apply subcapt_transitivity with (Q := cse_loc l); econstructor... *)
(*       eapply IHSub... *)
(*       rewrite <- subst_cse_fresh... *)
(*   - (* Case "subcapt_join_elim" *) *)
(*     epose proof (subst_cse_loc_invert_join _ _ _ _ _ x) as [C1' [C2' [Eq [Eq1 Eq2]]]]; subst. *)
(*     inversion WfC... *)
(* Qed. *)

Lemma subcapt_through_subst_cse_rev : forall Γ S C D R x l,
  subcapt Γ S (subst_cse x (cse_loc l) C) D ->
  wf_ctx ([(x, bind_typ (cse_loc l # R))] ++ Γ) S ->
  wf_cse ([(x, bind_typ (cse_loc l # R))] ++ Γ) S C ->
  subcapt ([(x, bind_typ (cse_loc l # R))] ++ Γ) S C D.
Proof with eauto using subcapt_reflexivity, wf_cse_weaken_head.
  intros * Sub WfCtx WfC.
  generalize dependent R.
  dependent induction Sub; intros...
  - (* Case "subcapt_bot". *)
    enough (C = cse_bot); subst...
    induction C; simpl in *; try discriminate...
    destruct (x0 == a); discriminate...
  - (* Case "subcapt_refl_var" *)
    enough (C = cse_fvar X); subst...
    induction C; simpl in *; try discriminate...
    destruct (x0 == a); inversion x...
  - (* Case "subcapt_refl_loc" *)
    enough (C = cse_loc l0 \/ (C = cse_fvar x0 /\ l0 = l)); subst...
    destruct H1 as [Eq | [Eq LocEq]]; subst...
    { simpl in x; destruct (x0 == x0); try fsetdec; econstructor... }
    induction C; simpl in *; try discriminate...
    destruct (x0 == a); try fsetdec; inversion x...
    right; split; f_equal...
  - (* Case "subcapt_trans_var" *)
    assert (WfR : wf_cse Γ S R) by applys subcapt_regular Sub.
    assert (x0 `notin`A cse_fvars R). {
      intro In.
      epose proof (wf_cse_fvars_from_ctx _ _ _ _ WfR In)...
      inversion WfCtx...
    }
    assert (C = cse_fvar X); subst. {
      induction C; simpl in *; try discriminate...
      destruct (x0 == a); inversion x...
    }
    econstructor...
    eapply IHSub...
    rewrite <- subst_cse_fresh...
  - (* Case "subcapt_trans_loc" *)
    assert (WfR : wf_cse Γ S R) by applys subcapt_regular Sub.
    assert (C = cse_loc l0 \/ (C = cse_fvar x0 /\ l0 = l)). {
      induction C; simpl in *; try discriminate...
      destruct (x0 == a); try fsetdec; inversion x...
      right; split; f_equal...
    }
    assert (x0 `notin`A cse_fvars R). {
      intro In.
      epose proof (wf_cse_fvars_from_ctx _ _ _ _ WfR In)...
      inversion WfCtx...
    }
    destruct H0 as [Eq | [Eq LocEq]]; subst...
    + econstructor...
      eapply IHSub...
      rewrite <- subst_cse_fresh...
    + apply subcapt_transitivity with (Q := cse_loc l); econstructor...
      eapply IHSub...
      rewrite <- subst_cse_fresh...
  - (* Case "subcapt_join_elim" *)
    epose proof (subst_cse_loc_invert_join _ _ _ _ _ x) as [C1' [C2' [Eq [Eq1 Eq2]]]]; subst.
    inversion WfC...
Qed.


(* Lemma subcapt_through_subst_cse : forall x D Q C Δ Γ S C1 C2 , *)
(*   subcapt (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) S C1 C2 -> *)
(*   subcapt Γ S C D -> *)
(*   subcapt (map (subst_cb x C) Δ ++ Γ) S (subst_cse x C C1) (subst_cse x C C2). *)

Lemma sub_through_subst_ct_rev_aux : forall Γ S U T R x l,
  no_type_bindings Γ ->
  sub Γ S (subst_ct x (cse_loc l) U) (subst_ct x (cse_loc l) T) ->
  wf_ctx ([(x, bind_typ (cse_loc l # R))] ++ Γ) S ->
  wf_typ ([(x, bind_typ (cse_loc l # R))] ++ Γ) S U ->
  wf_typ ([(x, bind_typ (cse_loc l # R))] ++ Γ) S T ->
  sub ([(x, bind_typ (cse_loc l # R))] ++ Γ) S U T.
Proof with eauto using type_from_wf_typ, sub_reflexivity, subcapt_through_subst_cse_rev_aux.
  intros * NoTypeBindings Sub WfCtx WfU WfT.
  generalize dependent R.
  dependent induction Sub; intros;
    try rename select (_ = subst_ct _ _ T) into EqT;
    try rename select (_ = subst_ct _ _ U) into EqU...
  - (* Case "sub_refl_tvar" *)
    assert (U = typ_var X); subst...
    { induction U; simpl in *; try discriminate...
      destruct v... }
    assert (T = typ_var X); subst...
    { induction T; simpl in *; try discriminate...
      destruct v... }
  - (* Case "sub_trans_tvar" *)
    exfalso. apply (NoTypeBindings _ _  H).
  - (* Case "sub_capt" *)
    symmetry in EqU.
    symmetry in EqT.
    destruct (subst_ct_invert_capt _ _ _ _ _ EqU) as [C' [R' [Eq' [C'Eq R'Eq]]]]; subst.
    destruct (subst_ct_invert_capt _ _ _ _ _ EqT) as [C'' [R'' [EqT' [C''Eq R''Eq]]]]; subst.
    inversion WfU; subst...
    inversion WfT; subst...
  - (* Case "sub_top" *)
    admit. (* subst_ct_pure_typ_rev *)
  - (* Case "sub_arr" *)
    symmetry in EqU.
    symmetry in EqT.
    destruct (subst_ct_invert_fun _ _ _ _ _ _ EqU) as [C' [R' [T' [Eq' [C1Eq [R1Eq T1Eq]]]]]]; subst.
    destruct (subst_ct_invert_fun _ _ _ _ _ _ EqT) as [C'' [R'' [T'' [EqT' [C2Eq [R2Eq T2Eq]]]]]]; subst.
    pick fresh y and apply sub_arr...
    (* eapply sub_arr with (C1 := C') (R1 := R') (C2 := C'') (R2 := R'')... *)
    (* eapply IHSub... *)
    (* rewrite <- subst_ct_fresh... *)
    (* rewrite <- subst_ct_fresh... *)
    (* eapply wf_typ_subst_ct... *)
    (* eapply wf_typ_subst_ct... *)
    (* inversion WfU; subst. *)
    (* inversion H8; subst. *)
Admitted.


(* Lemma sub_through_subst_ct_rev_test : forall Γ S T R x l, *)
(*   no_type_bindings Γ -> *)
(*   wf_ctx ([(x, bind_typ (cse_loc l # R))] ++ Γ) S -> *)
(*   wf_typ ([(x, bind_typ (cse_loc l # R))] ++ Γ) S T -> *)
(*   sub ([(x, bind_typ (cse_loc l # R))] ++ Γ) S T (subst_ct x (cse_loc l) T). *)
(* Proof with eauto using type_from_wf_typ, sub_reflexivity, subcapt_through_subst_cse_rev. *)
(*   intros * NoTypeBindings WfCtx WfT. *)
(*   generalize dependent R. *)
(*   dependent induction T; intros; simpl... *)
(*   - destruct v... *)
(*   - s *)

Lemma sub_through_subst_ct_rev : forall Γ S U T R x l,
  no_type_bindings Γ ->
  sub Γ S (subst_ct x (cse_loc l) U) T ->
  wf_ctx ([(x, bind_typ (cse_loc l # R))] ++ Γ) S ->
  wf_typ ([(x, bind_typ (cse_loc l # R))] ++ Γ) S U ->
  sub ([(x, bind_typ (cse_loc l # R))] ++ Γ) S U T.
Proof with eauto using type_from_wf_typ, sub_reflexivity, subcapt_through_subst_cse_rev.
  intros * NoTypeBindings Sub WfCtx WfU.
  generalize dependent R.
  dependent induction Sub; intros; try rename select (_ = _) into Eq...
  - (* Case "sub_refl_tvar" *)
    enough (U = typ_var X); subst...
    induction U; simpl in *; try discriminate...
    destruct v...
  - (* Case "sub_trans_tvar" *)
    exfalso. apply (NoTypeBindings _ _  H).
  - (* Case "sub_capt" *)
    symmetry in Eq.
    destruct (subst_ct_invert_capt _ _ _ _ _ Eq) as [C' [R' [Eq' [C'Eq R'Eq]]]]; subst.
    inversion WfU...
  - (* Case "sub_top" *)
    admit. (* subst_ct_pure_typ_rev *)
  - (* Case "sub_arr" *)
    symmetry in Eq.
    destruct (subst_ct_invert_fun _ _ _ _ _ _ Eq) as [C' [R' [T' [Eq' [C1Eq [R1Eq T1Eq]]]]]]; subst.
    (* inversion WfU; subst. *)
    (* inversion H8; subst. *)
    pick fresh y and apply sub_arr...
    Admitted.

Lemma loc_transform_sub : forall Γ E U U' S,
  env_well_typed S E Γ ->
  wf_typ Γ S U ->
  loc_transform E U U' ->
  sub Γ S U U'.
Proof with eauto using sub_reflexivity, runtime_ctx_no_type_bindings.
  intros * EnvTyp WfU LocTrans.
  generalize dependent Γ.
  generalize dependent S.
  dependent induction LocTrans; intros; inversion EnvTyp; subst...
  eapply sub_through_subst_ct_rev...
  eapply IHLocTrans...
  rewrite_env (nil ++ Γ0).
  replace nil with (map (subst_cb x (cse_loc l)) nil) at 1 by reflexivity.
  eapply wf_typ_subst_cb...
Qed.

Lemma frame_typing_sub : forall S E e U T,
  sub nil S U T ->
  frame_typing S (e, E) U ->
  frame_typing S (e, E) T.
Proof with eauto using sub_reflexivity, loc_transform_ident, wf_typ_notin_fv_ct.
  intros * Sub Frame.
  inversion Frame; subst.
  rename select (env_well_typed _ _ _) into EnvTyp.
  rename select (typing _ _ _ _) into Typ.
  assert (WfT : wf_typ nil S T) by applys sub_regular Sub.
  assert (SubWeak : sub Γ S U T). {
    rewrite_env (nil ++ Γ ++ nil).
    apply sub_weakening...
    simpl_env...
  }
  unshelve epose proof (loc_transform_sub _ _ _ _ _ EnvTyp _ H5) as SubU0U...
  assert (typing Γ S e U) by (eapply typing_sub; eauto).
  assert (typing Γ S e T) by (eapply typing_sub; eauto).
  econstructor...
Qed.

(* Lemma frame_typing_inv_abs : forall S E lx e1 C C0 R0 C1 R1 U, *)
(*   frame_typing S (λ (C0 # R0) e1, E) (C # (∀ (C1 # R1) U)) -> *)
(*   StoreImpl.binds lx (C0 # R0) S -> *)
(*   exists Γ S2 L, *)
(*   (forall x, x ∉ L -> *)
(*     env_well_typed S E Γ -> *)
(*     frame_typing S (open_ve e1 x (cse_fvar x), (x ~ lx) ++ E) (open_ct S2 (cse_loc lx)) /\ *)
(*     sub ([(x, bind_typ (C1 # R1))] ++ Γ) S (open_ct S2 (cse_loc lx)) (open_ct U (cse_fvar x))). *)
(* Proof with eauto using sub_reflexivity, subcapt_reflexivity. *)
(*   intros * Frame Binds. *)
(*   inversion Frame; subst. *)
(*   rename select (env_well_typed _ _ _) into EnvTyp. *)
(*   rename select (typing _ _ _ _) into Typ. *)
(*   epose proof (loc_transform_capt_rev _ _ _ _ H5) as [C' [Fun' [LocTransC' [LocTransFun' Eq]]]]; subst. *)
(*   epose proof (loc_transform_fun_rev _ _ _ _ _ LocTransFun') as [C0' [R0' [U' [LocTransC0' [LocTransR' [LocTransU' Eq]]]]]]; subst. *)
(*   unshelve epose proof (typing_inv_abs _ _ _ _ _ Typ (C0' # R0') U' C') as [Sub [S2 [L Ret]]]... *)
(*   exists Γ, S2, (L `union`A dom E `union`A fv_ct U'). *)
(*   intros * Fr _. *)
(*   assert (NotIn: x `notin`A dom Γ). *)
(*   { rewrite <- (env_well_typed_preserves_dom _ _ _ EnvTyp); fsetdec. } *)
(*   repeat split... *)
(*   - eapply typing_frame. *)
(*     + econstructor... *)
(*     + destruct (Ret x ltac:(fsetdec)) as [e1Typ [WfS2 SubS2]]. *)
(*       rewrite_env (nil ++ [(x, bind_typ (cse_loc lx # R0))] ++ Γ). *)
(*       eapply typing_narrowing_typ... *)
(*       assert (WfC0R0 : wf_typ Γ S (C0 # R0)) by applys sub_regular Sub. *)
(*       inversion WfC0R0; subst... *)
(*       constructor... *)
(*     + admit. *)
(*   -  *)
(*    *)
(*   (* with (Γ := (x ~ bind_typ (cse_loc lx # R0)) ++ Γ). *) *)
(*   (* (U := open_ct U' (cse_fvar x))... *) *)
(*   - econstructor... *)
(*   - destruct (Ret x ltac:(fsetdec)) as [e1Typ [Wf SubS2]]. *)
(*     admit. *)
(*   - eapply loc_transform_open_ct_bound_var... *)
(*     econstructor... *)
(*     constructor... *)
(*     rewrite <- subst_ct_fresh... *)
(* Admitted. *)

Lemma preservation : forall Σ Σ' V,
  state_typing Σ V ->
  red Σ Σ' ->
  state_typing Σ' V.
Proof with eauto.
  intros * [S E SS K C1 R1 C2 R2 e StoreTyp EvalTyp FrameTyp] Red.
  (* inversion FrameTyp; subst. *)
  (* rename select (env_well_typed _ _ _) into EnvTyp. *)
  assert (WfC1R1 : wf_typ nil S (C1 # R1)) by applys frame_typing_regular FrameTyp.
  (* rename select (typing _ _ _ _) into Typ. *)
  dependent induction Red; intros.
  - (* Case "red_app". *)
    (* eapply typing_state... *)
    (* eapply typing_frame. *)
    epose proof frame_typing_inv_app.
    destruct (frame_typing_inv_app _ _ _ _ _ _ H0 FrameTyp) as [C9 [D [Q [U0 [xTyp [yTyp USubC1R1]]]]]].
    econstructor...
    (* destruct (typing_inv_app _ _ _ _ _ Typ) as [C9 [D [Q [U0 [xTyp [yTyp USubC1R1]]]]]]. *)
  epose proof (loc_transform_result ((∀ ((D # Q)) U0)) E) as [TFun LocTransDQ].
    epose proof (loc_transform_fun _ _ _ _ _ LocTransDQ) as [D' [Q' [U' [LocTransD [LocTransQ [LocTransU Eq'']]]]]]; subst...
    (* epose proof (loc_transform_cse_result C9 E) as [C9' LocTransC9]. *)
    (* assert (frame_typing S (exp_var x, E) (C9' # (∀ ((D' # Q')) U'))). { *)
    (*   econstructor... *)
    (*   eapply (proj2 (loc_transform_equiv _ _ _ _ _))... *)
    (*   admit. *)
    (* } *)
    destruct ((proj2 (store_typing_equivalent _ _ lx StoreTyp))) as [C0 [R0 Binds]].
    eexists...
    econstructor...
    destruct (store_typing_inversion _ _ _ _ _ _ StoreTyp Binds H1) as [Γ0 [C3 [R3 [absTyp [EnvTyp2 [LocTransC3R3 Val]]]]]].
    assert (xBinds : binds x (bind_typ (cse_loc lx # R0)) Γ). {
      apply (proj1 (env_typing_inversion _ _ _ R0 _ _ EnvTyp H))...
    }
    destruct (typing_var_implies_binds_typ _ _ _ _ _ xTyp) as [D0 [Q0 [xBinds2 [xSubD0 [_ [R0SubFun PureFun]]]]]].
    epose proof (binds_unique _ _ _ _ _ xBinds2 xBinds _) as Eq; inversion Eq; subst; clear Eq.
    destruct v as [v E1].
    destruct ((proj2 (store_typing_equivalent _ _ ly StoreTyp))) as [D0 [Q0 Binds']].
    exists v, E1...
    assert (yBinds : binds y (bind_typ (cse_loc ly # Q0)) Γ). {
      apply (proj1 (env_typing_inversion _ _ _ Q0 _ _ EnvTyp H0))...
    }
    destruct (typing_var_implies_binds_typ _ _ _ _ _ yTyp) as [D1 [Q1 [yBinds2 [ySubD1 [_ [Q1SubQ PureQ]]]]]].
    epose proof (binds_unique _ _ _ _ _ yBinds2 yBinds _) as Eq; inversion Eq; subst; clear Eq.
    epose proof (typing_inv_abs _ _ _ _ _ absTyp).
    econstructor...
    eapply typing_frame with (Γ := ([(z, bind_typ (cse_loc ly # Q0))] ++ Γ0))...
    + simpl_env.
      epose proof (env_well_typed_preserves_dom _ _ _ EnvTyp2).
      apply env_cons with (C := D0)...
      rewrite <- H4...
    +
      epose proof (loc_transform_result ((∀ ((D # Q)) U)) E) as [TFun LocTransDQ].
      epose proof (loc_transform_fun _ _ _ _ _ LocTransDQ) as [D' [Q' [U' [LocTransD [LocTransQ [LocTransU Eq'']]]]]]; subst...
      epose proof (loc_transform_ident E R0 _) as LocTransR0...
      epose proof (sub_under_loc_transform _ _ _ _ _ _ _ EnvTyp LocTransR0 LocTransDQ R0SubFun).
      epose proof (typing_inv_abs _ _ _ _ _ absTyp).

      admit.
    + unshelve epose proof (loc_transform_result (∀ ((D # Q)) U) _ _ _ EnvTyp _) as [T2 LocTransDQ]...
      destruct (loc_transform_fun _ _ _ _ _ LocTransDQ) as [D1 [Q1 [T1 [LocTransD [LocTransQ [LocTransU Eq]]]]]]; subst...
      unshelve epose proof (loc_transform_ident E R0 _)...
      epose proof (sub_under_loc_transform).

      assert (WfU : wf_typ Γ S (open_ct U (cse_fvar y))) by applys sub_regular USubC1R1.
      destruct (loc_transform_result _ _ _ _ EnvTyp WfU) as [U0 LocTransU].
      epose proof (sub_under_loc_transform _ _ _ _ _ _ _ EnvTyp LocTransU H5 USubC1R1).
      epose proof (typing_inv_abs _ _ _ _ _ absTyp).
      clear - USubC1R1 WfC1R1 EvalTyp.
      admit.
    + 

Lemma preservation : forall Σ Σ' V,
  prec_state_typing Σ V ->
  red Σ Σ' ->
  prec_state_typing Σ' V.
Proof with eauto*.
  intros * [Γ Γ' S E SS K C1 R1 C2 R2 e PStoreTyp EvalTyp PTyp EnvTyp] Red.
  (* assert (Typ : typing Γ S e (C1 # R1)). *)
  (* { eapply prec_typing_implies_typing; eauto. } *)
  (* assert (WfStore : wf_store_ctx S) by applys typed_store_ctx_wf StoreTyp. *)
  dependent induction Red.
  - Case "red_app".
    inversion PTyp; subst.
    (* rename select (_ = _) into Eq. *)
    (* destruct (open_ct_invert _ _ _ _ Eq) as [C4 [R4 [Eq' [C4Eq R4Eq]]]]. *)
    (* subst... *)
    (* inversion select (prec_typing _ _ x _); subst. *)
    (* rename select (binds _ _ Γ) into xBindsΓ. *)
    (* destruct (env_typing_inversion _ _ _ _ _ _ _ EnvTyp H) as [StoreBindsx [xBindsΓ2 WfC0R0]]. *)
    (* epose proof (binds_unique _ _ _ _ xBindsΓ xBindsΓ2) as Eq; inverts Eq. *)
    (* inversion select (prec_typing _ _ y _); subst. *)
    (* destruct (env_typing_inversion _ _ _ _ _ _ _ EnvTyp H0) as [StoreBindsy [yBindsΓ WfC3R3]]. *)
    (* epose proof (binds_unique _ _ _ _ H14 yBindsΓ) as Eq; inverts Eq. *)
    rename select (prec_typing _ _ x _) into xPTyp.
    destruct (stores_preserves_typing _ _ _ _ _ _ _ _ _ _ PStoreTyp EnvTyp H H1 xPTyp) as [Γ0 [absTyp EnvTyp2]].
    simpl in absTyp.
    inversion absTyp; subst.

    rename select (prec_typing _ _ y _) into yPTyp.
    inverts yPTyp.
    rename select (binds y _ _) into yBinds.
    epose proof ((proj2 (env_typing_inversion _ _ _ _ _ _ _ EnvTyp H0)) yBinds).

    erewrite env_well_typed_preserves_dom in H3...
    rename select (forall (x: atom), x ∉ L -> prec_typing _ _ _ _) into e1Typ.
    pick fresh z0 and specialize e1Typ.
    eapply prec_typing_state with (Γ := ([(z, bind_typ (C0 # Q))] ++ Γ0))...
    + replace (C1 # R1) with (open_ct T0 (cse_fvar y)).
      admit.
      (* apply prec_typing_weakening with (Θ := [(z, bind_typ (C3 # R3))]) in e1Typ. *)
      (* * replace (C1 # R1) with (open_ct (C1 # R1) (cse_fvar z)). *)
      (*   2: { *)
      (*     unfold open_ct. *)
      (*     erewrite open_ct_rec_type... *)
      (*     eapply type_from_wf_typ... *)
      (*   } *)
      (*   apply prec_typing_through_open_ve_typing_open with (y := z0) (U := D # Q)... *)
      (*   admit. *)
      (* * simpl; constructor... *)
      (*   -- epose proof (wf_typ_weaken_head _ _ Γ0 _ WfC3R3). *)
      (*      simpl_env in H4... *)
      (*      constructor... *)
      (*   -- rewrite_env (nil ++ [(z, bind_typ (C3 # R3))] ++ Γ0). *)
      (*      apply wf_typ_weakening... *)
      (*      constructor... *)
    + constructor...
  - Case "red_tapp".
    inversion PTyp; subst.
    inversion select (prec_typing _ _ x _); subst.
    rename select (binds x _ _) into xBindsΓ.
    epose proof ((proj2 (env_typing_inversion _ _ _ _ _ _ _ EnvTyp H)) xBindsΓ) as StoreBinds.
    (* destruct (env_typing_inversion _ _ _ _ _ _ _ EnvTyp H) as [StoreBindsx [Binds WfCR]]. *)
    (* epose proof (binds_unique _ _ _ _ Binds H10) as Eq. *)
    (* symmetry in Eq; inverts Eq. *)
    rename select (prec_typing _ _ x _) into xPTyp.
    destruct (stores_preserves_typing _ _ _ _ _ _ _ _ _ _ PStoreTyp EnvTyp H H0 xPTyp) as [Γ0 [tabsTyp EnvTyp2]].
    simpl in tabsTyp.
    inversion tabsTyp; subst.
    rename select (forall (X: atom), X ∉ L -> prec_typing _ _ _ _) into e1Typ.
    pick fresh Z and specialize e1Typ.
    eapply prec_typing_state with (Γ := Γ0)...
    replace (C1 # R1) with (open_tt T1 T).
    apply prec_typing_through_open_te with (Y := Z) (Q := Q)...
    admit.
  - Case "red_let".
    inversion PTyp; subst.
    eapply prec_typing_state...
    apply prec_typing_eval_cons with (L := L) (C2 := C1) (R2 := R1)...

  - Case "red_lift".
    inversion EvalTyp; subst.
    rename select (forall x, x ∉ L -> typing _ _ _ _) into Typ'.
    eapply typing_state with (S := [(l, (C1 # R1))] ++ S).
    + apply typing_store_cons...
      rewrite <- store_typing_preserves_dom with (E := E)...
    + Store.rewrite_nil_concat.
      apply eval_typing_weakening_store...
      simpl. constructor...
      rewrite <- store_typing_preserves_dom with (E := E)...
    + pick fresh y and specialize Typ'.
      assert (l `Notin` Store.dom S) by (rewrite <- store_typing_preserves_dom with (E := E); assumption).
      assert (WfStore' : wf_store_ctx ([(l, (C1 # R1))] ++ S)) by (constructor; eauto*).
      eapply typing_through_open_ve_typing_loc with (y := y) (U := C1 # R1).
      * simpl; clear - Fr; fsetdec.
      * Store.rewrite_nil_concat. apply typing_weakening_store.
        1: assumption.
        eauto.
      * apply typing_sub with (R := (cse_loc l # R1))...
        inversion WfC1R1; subst...
        constructor...
        -- eapply subcapt_trans_loc...
           apply subcapt_reflexivity...
           rewrite_env (nil ++ [(l, C1 # R1)] ++ S).
            apply wf_cse_weakening_store...
        -- apply sub_reflexivity...
           rewrite_env (nil ++ [(l, C1 # R1)] ++ S).
           apply wf_typ_weakening_store...
  - Case "red_loc".
    inversion EvalTyp; subst.
    rename select (forall x, x ∉ L -> typing _ _ _ _) into Typ'.
    eapply typing_state with (StoreEnv := E)...
    pick fresh y and specialize Typ'.
    eapply typing_through_open_ve_typing_loc with (y := y)...
  - Case "red_let_val".
    destruct (typing_inv_let _ _ _ _ _ Typ) as [D [Q [vTyp [L kTyp]]]].
    assert (WfDQ : wf_typ nil S (D # Q)) by applys typing_regular vTyp.
    eapply typing_state with (S := ([(l, (D # Q))] ++ S))...
    + apply typing_store_cons...
      rewrite <- store_typing_preserves_dom with (E := E)...
    + Store.rewrite_nil_concat.
      apply eval_typing_weakening_store...
      simpl. constructor...
      rewrite <- store_typing_preserves_dom with (E := E)...
    + pick fresh y and specialize kTyp.
      assert (l `Notin` Store.dom S) by (rewrite <- store_typing_preserves_dom with (E := E); assumption).
      assert (WfStore' : wf_store_ctx ([(l, (D # Q))] ++ S)) by (constructor; eauto*).
      eapply typing_through_open_ve_typing_loc with (y := y) (U := D # Q)...
      * simpl in *.
        rewrite_env (nil ++ S) in kTyp.
        unshelve epose proof (typing_weakening_store _ _ _ _ [(l, D # Q)] _ kTyp ltac:(eauto)) as kTyp'.
        simpl_env in kTyp'...
      * apply typing_sub with (R := (cse_loc l # Q))...
        inversion WfDQ; subst...
        constructor...
        -- eapply subcapt_trans_loc...
           apply subcapt_reflexivity...
           rewrite_env (nil ++ [(l, D # Q)] ++ S).
           apply wf_cse_weakening_store...
        -- apply sub_reflexivity...
           rewrite_env (nil ++ [(l, D # Q)] ++ S).
           apply wf_typ_weakening_store...
  - Case "red_let_exp".
    destruct (typing_inv_let _ _ _ _ _ Typ) as [D [Q [vTyp [L kTyp]]]].
    assert (WfDQ : wf_typ nil S (D # Q)) by applys typing_regular vTyp.
    eapply typing_state...
  - Case "red_app".
    destruct (typing_inv_app _ _ _ _ _ Typ) as [C [D [Q [T [fTyp [xTyp T2SubT]]]]]].
    rename select (stores E f _) into fStores.
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp fStores fTyp) as [D' [Q' [absTyp [fBinds [e0subD QsubP]]]]].
    simpl in absTyp, e0subD.
    destruct (typing_inv_abs _ _ _ _ _ absTyp (D # Q) T (exp_cv e0)) as [T1subU0 [S2 [L Ret]]].
    1: {
      assert (PureQ' : pure_type Q').
      { enough (WfD'Q' : wf_typ nil S (D' # Q')) by (inversion WfD'Q'; auto).
        eapply wf_pair_from_wf_store_ctx...
      }
      apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QsubP...
    }
    pick fresh z and specialize Ret.
    destruct Ret as [e0Typ [WfT2 S2SubT2]].
    eapply typing_state...
    apply typing_sub with (R := open_ct T (cse_loc l))...
    destruct (proj1 (sub_capt_type _ _ _ _ T1subU0)) as [D'' [Q'' Eq]]; subst. exists D, Q...
    apply typing_through_open_ve_typing_open_loc with (y := z) (U := D # Q).
      * clear - Fr. fsetdec.
      * apply typing_sub with (R := open_ct S2 (cse_fvar z))...
        rewrite_nil_concat. eapply typing_narrowing_typ...
      * eapply typing_sub, sub_reflexivity...
  - Case "red_tapp".
    destruct (typing_inv_tapp _ _ _ _ _ Typ) as [C [R' [U' [lTyp VsubQ]]]].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp H lTyp) as [D [Q [tabsTyp [lBinds [e0subD QsubP]]]]].
    simpl in tabsTyp, e0subD.
    assert (PureQ : pure_type Q).
    { enough (WfDQ : wf_typ nil S (D # Q)) by (inversion WfDQ; assumption).
      eapply wf_pair_from_wf_store_ctx...
    }
    assert (e0Qsube0subU' : sub nil S (exp_cv e0 # Q) (exp_cv e0 # ∀ [R'] U')).
    { apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QsubP...
    }
    destruct (typing_inv_tabs _ _ _ _ _ tabsTyp R' U' (exp_cv e0) e0Qsube0subU') as [T1SubU0 [S2 [L Ret]]].
    pick fresh Z and specialize Ret.
    destruct Ret as [WfS2 S2subT2].
    eapply typing_state...
    apply typing_sub with (R := open_tt U' R)...
    eapply typing_through_open_te with (Y := Z)...
  - Case "red_open".
    destruct (typing_inv_unbox _ _ _ _ _ Typ) as [R [lTyp CRsubC1R1]].
    rename select (stores E l _) into lStores.
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp lStores lTyp) as [D' [Q' [boxTyp [lBinds [ysubD QsubP]]]]].
    destruct (typing_inv_box _ _ _ _ boxTyp) as [D [Q [yTyp [CsubΓ BoxCRsubT]]]].
    simpl in boxTyp, ysubD, BoxCRsubT.
    eapply typing_state...
    apply typing_sub with (R := D # Q)...
    inversion BoxCRsubT; subst.
    assert (sub nil S (□ D # Q) (□ C # R)) by (apply sub_transitivity with (Q := Q'); eauto).
    inversion select (sub nil S (□ _) (□ _)); subst.
    apply sub_transitivity with (Q := C # R)...
Qed.

Lemma binds_implies_store : forall S E l T,
  store_typing E S ->
  Store.binds l T S ->
  exists v, stores E l v.
Proof with eauto*.
  intros * StoreTyp Binds.
  induction StoreTyp.
  - inversion Binds.
  - destruct (l ==== l0); subst...
    + SCase "l = l0".
      exists v.
      rewrite Store.cons_concat.
      apply Store.binds_head...
      apply Store.binds_singleton...
    + Case "l <> l0".
      rename select (Store.binds l _ _) into Binds.
      rewrite Store.cons_concat in *.
      Store.binds_cases Binds...
      * destruct (IHStoreTyp H2) as [w Stores].
        exists w.
        apply Store.binds_tail...
      * exfalso.
        apply Store.binds_In in H3. simpl in H3.
        flsetdec.
Qed.

(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall S v C U1 U2,
  value v ->
  typing nil S v (C # (∀ (U1) U2)) ->
  exists S1 e, v = λ (S1) e
             /\ sub nil S U1 S1.
Proof with eauto*.
  intros * Val Typ.
  remember (∀ (U1) U2).
  revert U1 U2 Heqt.
  assert (WfStore : wf_store_ctx S) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - Case "typing_abs".
    inversion Eq; subst.
    exists (C0 # R), e1.
    repeat split...
    eapply sub_reflexivity...
  - Case "typing_sub".
    destruct (proj2 (sub_capt_type _ _ _ _ H) ltac:(eauto)) as [D [Q Eq]]; subst.
    inversion select (sub _ _ _ _); subst.
    inversion select (sub _  _ _ (∀ (_) _)); subst.
    + inversion select (binds _ _ nil).
    + destruct (IHTyp D Val (∀ (C1 # R1) T1) eq_refl eq_refl WfStore (C1 # R1) T1 eq_refl) as [S' [e' [Eq Sub]]].
      exists S', e'.
      repeat split...
      apply sub_transitivity with (Q := C1 # R1)...
Qed.

Lemma canonical_form_tabs : forall S v C U1 U2,
  value v ->
  typing nil S v (C # ∀ [U1] U2) ->
  exists S1 e, v = Λ [S1] e
            /\ sub nil S U1 S1.
Proof with eauto*.
  intros * Val Typ.
  remember (∀ [U1] U2).
  revert U1 U2 Heqt.
  assert (WfStore : wf_store_ctx S) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - Case "typing_tabs".
    inversion Eq; subst.
    exists U1, e1.
    repeat split...
    eapply sub_reflexivity...
  - Case "typing_sub".
    destruct (proj2 (sub_capt_type _ _ _ _ H) ltac:(eauto)) as [D [Q Eq]]; subst.
    inversion select (sub _ _ _ _); subst.
    inversion select (sub _ _ _ (∀ [_] _)); subst.
    + inversion select (binds _ _ nil).
    + destruct (IHTyp D Val (∀ [R1] T1) eq_refl eq_refl WfStore R1 T1 eq_refl) as [S' [e' [Eq Sub]]].
      exists S', e'.
      repeat split...
      apply sub_transitivity with (Q := R1)...
Qed.

Lemma canonical_form_box : forall S v D C R,
  value v ->
  typing nil S v (D # (□ C # R)) ->
  exists x, v = box x.
Proof with eauto*.
  intros * Val Typ.
  remember (D # (□ C # R)).
  forwards (WfStore & _ & _ & Wft): typing_regular Typ.
  assert (Sub : sub nil S t (D # (□ C # R))).
  { rewrite <- Heqt.
    apply sub_reflexivity...
  }
  clear Heqt.
  revert R Sub.
  dependent induction Typ; intros R' Sub; subst; try solve [ inversion Val | inversion Sub; inversion select (sub _ _ _ (□ _)) ].
  - Case "typing_box".
    exists x.
    repeat split...
  - Case "typing_sub".
    assert (sub nil S R (D # (□ C # R'))).
    { apply sub_transitivity with (Q := T)... }
    destruct (proj2 (sub_capt_type _ _ _ _ H0) ltac:(eauto)) as [D' [Q' Eq]]; subst.
    inversion select (sub nil S (D' # Q') (D # (□ C # R'))); subst.
    inversion select (sub _ _ Q' (□ C # R')); subst.
    + inversion select (binds _ _ nil).
    + assert (WfDBT1 : wf_typ nil S (D' # (□ T1))) by applys sub_regular H0.
      destruct (IHTyp Val eq_refl WfStore WfDBT1 R') as [e' Sub']...
Qed.

(* Lemma typing_fvar_like_implies_binds_typ : forall Γ e C R S, *)
(*   fval_like e -> *)
(*   typing Γ S e (C # R) -> *)
(*   exists D Q, binds x (bind_typ (D # Q)) Γ *)
(*            /\ subcapt Γ S (exp_cv e) C *)
(*            /\ wf_cse Γ S D *)
(*            /\ sub Γ S Q R *)
(*            /\ pure_type R. *)

Lemma progress : forall Σ V,
  state_typing Σ V ->
  state_final Σ \/ exists Σ', Σ --> Σ'.
Proof with eauto*.
  intros * [S E Sf C1 R1 C2 R2 e StoreTyp EvalTyp Typ].
  eremember (C1 # R1) as T.
  forwards (WfStore & _ & _ & WfT): typing_regular Typ.
  assert (sub nil S T (C1 # R1)).
  { rewrite <- HeqT; apply sub_reflexivity... }
  clear HeqT.
  generalize dependent R1.
  generalize dependent C1.
  dependent induction Typ; intros C' R' Sub.
  - Case "typing_var".
    inversion select (binds _ _ nil).
  - Case "typing_loc".
    inversion EvalTyp; subst.
    + left; apply final_state, answer_loc.
    + right.
      exists ⟨ E | Sf0 | open_ve k l (cse_loc l) ⟩.
      destruct (binds_implies_store _ _ _ _ StoreTyp H0) as [v Stores].
      eapply red_loc...
  - Case "typing_abs".
    assert (Val : value (exp_abs (C # R) e1)).
    { apply value_abs.
      apply expr_abs with (L := L).
      * eapply type_from_wf_typ, H.
      * intros x NotIn.
        rename select (forall x : atom, x ∉ L -> typing _ _ _ _) into Typ.
        specialize (Typ x NotIn).
        applys typing_regular Typ.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick lfresh l for (Store.dom E).
      exists ⟨ [(l, store (λ (C # R) e1))] ++ E | Sf0 | open_ve k l (cse_loc l) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_app".
    right.
    inversion H; subst.
    + exfalso.
      destruct (typing_var_implies_binds_typ _ _ _ _ _ Typ1) as [Cf [Rf [fBinds _]]].
      inversion fBinds.
    + destruct (typing_loc_implies_binds _ _ _ _ _ Typ1) as [Cf [Rf [fBinds [fsubC [WfCf [RfsubDQT PureDQT]]]]]].
      destruct (binds_implies_store _ _ _ _ StoreTyp fBinds) as [abs absStores].
      inversion H0; subst.
      * exfalso.
        destruct (typing_var_implies_binds_typ _ _ _ _ _ Typ2) as [Cx [Rx [xBinds _]]].
        inversion xBinds.
      * rename l into f.
        rename l0 into x.
        destruct (typing_loc_implies_binds _ _ _ _ _ Typ2) as [Cx [Rx [xBinds [xsubD [WfCx [RxsubQ PureQ]]]]]].
        destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [arg argStores].
        destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp absStores Typ1) as [Df [Qf [absTyp [fBinds' [absSubCf QfsubDQT]]]]].
        destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp argStores Typ2) as [Dx [Qx [argTyp [xBinds' [argSubCx QxsubQ]]]]].
        apply typing_sub with (T := exp_cv abs # (∀ ((D # Q)) T)) in absTyp.
        2: {
          apply sub_capt...
          - apply subcapt_reflexivity...
          - enough (WfDfQf : wf_typ nil S (Df # Qf)) by (inversion WfDfQf; assumption).
            eapply wf_typ_from_wf_store_ctx...
        }
        assert (absValue : value abs) by (eapply env_implies_value; eauto).
        destruct (canonical_form_abs _ _ _ _ _ absValue absTyp) as [S1 [e [Eq DQsubS1]]].
        rewrite Eq in *.
        assert (absValue' : value (λ (S1) e)).
        { inversion absValue; subst... }
        exists ⟨ E | Sf | open_ve e x (cse_loc x) ⟩.
        eapply red_app...
  - Case "typing_let".
    right.
    pick lfresh l for (Store.dom S).
    assert (k_scope : scope k).
    { econstructor.
      intros x NotIn.
      rename select (forall x : atom, x ∉ L -> typing _ _ _ _) into Typ'.
      specialize (Typ' x NotIn).
      applys typing_regular Typ'.
    }
    exists ⟨ E | k :: Sf | e ⟩.
    apply red_let_exp, k_scope.
  - Case "typing_tabs".
    assert (Val : value (exp_tabs V0 e1)).
    { apply value_tabs.
      apply expr_tabs with (L := L)...
      intros x NotIn.
      rename select (forall X : atom, X ∉ L -> typing _ _ _ _) into Typ.
      specialize (Typ x NotIn).
      applys typing_regular Typ.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick lfresh l for (Store.dom E).
      exists ⟨ [(l, store (Λ [V0] e1))] ++ E | Sf0 | open_ve k l (cse_loc l) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_tapp".
    right.
    inversion H; subst.
    + exfalso.
      destruct (typing_var_implies_binds_typ _ _ _ _ _ Typ) as [Cx [Rx [xBinds _]]].
      inversion xBinds.
    + destruct (typing_loc_implies_binds _ _ _ _ _ Typ) as [Cx [Rx [xBinds [xsubC [WfCx [RxsubQT PureQT]]]]]].
      rename l into x.
      destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [tabs tabsStores].
      destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp tabsStores Typ) as [Dx [Qx [tabsTyp [fBinds' [tabsSubCx QfsubQT]]]]].
      apply typing_sub with (T := exp_cv tabs # (∀ [Q] T)) in tabsTyp.
      2: {
        apply sub_capt...
        - apply subcapt_reflexivity...
        - applys sub_pure_type QfsubQT...
      }
      assert (tabsValue : value tabs) by (eapply env_implies_value; eauto).
      destruct (canonical_form_tabs _ _ _ _ _ tabsValue tabsTyp) as [S1 [e [Eq DQsubS1]]].
      rewrite Eq in *.
      assert (tabsValue' : value (Λ [S1] e)).
      { inversion tabsValue; subst... }
      exists ⟨ E | Sf | open_te e P ⟩.
      eapply red_tapp...
      assert (PureQ : pure_type Q) by (inversion PureQT; assumption).
      applys sub_pure_type H0...
  - Case "typing_box".
    assert (Val : value (box x)).
    { apply value_box... }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick lfresh l for (Store.dom E).
      exists ⟨ [(l, store (box x))] ++ E | Sf0 | open_ve k l (cse_loc l) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_unbox".
    right.
    inversion H; subst.
    + exfalso.
      destruct (typing_var_implies_binds_typ _ _ _ _ _ Typ) as [Cx [Rx [xBinds _]]].
      inversion xBinds.
    + destruct (typing_loc_implies_binds _ _ _ _ _ Typ) as [Cx [Rx [xBinds [xsubC [WfCx [RxsubQT PureQT]]]]]].
      rename l into x.
      destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [box' boxStores].
      destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp boxStores Typ) as [Dx [Qx [boxTyp [xBinds' [boxSubCx QxsubQT]]]]].
      apply typing_sub with (T := exp_cv box' # (□ C # R)) in boxTyp.
      2: {
        apply sub_capt...
        - apply subcapt_reflexivity...
        - applys sub_pure_type QxsubQT...
      }
      assert (boxValue : value box') by (eapply env_implies_value; eauto).
      destruct (canonical_form_box _ _ _ _ _ boxValue boxTyp) as [y Eq].
      rewrite Eq in *.
      assert (boxValue' : value (box y)).
      { inversion boxValue; subst... }
      exists ⟨ E | Sf | y ⟩.
      eapply red_open...
  - Case "typing_sub".
    eapply IHTyp...
    + eapply eval_typing_sub with (R1 := T) (T1 := C2 # R2)...
      eapply sub_reflexivity...
      applys eval_typing_regular EvalTyp.
    + apply sub_transitivity with (Q := T)...
Qed.
