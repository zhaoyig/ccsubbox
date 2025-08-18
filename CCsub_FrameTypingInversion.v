Require Import Coq.Program.Equality.
Require Import LibTactics.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.
Require Import CCsub_Red.
Require Import CCsub_Inversion.
Require Import CCsub_RuntimeInversion.
Require Import CCsub_LocTransform.

Lemma frame_typing_fv_ve_ce_in_env : forall S E e T,
  frame_typing S (e, E) T ->
  forall x,
    x `notin`A dom E ->
    x `notin`A fv_ve e `union`A fv_ce e.
Proof with eauto.
  intros * Frame x NotIn.
  dependent induction Frame; subst; intros.
  - rewrite (env_well_typed_preserves_dom _ _ _ H) in NotIn.
    eapply typing_fv_ve_fv_ce...
  - eapply IHFrame...
Qed.

Lemma store_binds_typ_sub : forall S E Γ x lx C R C1 R1,
  env_well_typed S E Γ ->
  binds x lx E ->
  StoreImpl.binds lx (C # R) S ->
  typing Γ S x (C1 # R1) ->
  sub Γ S R R1.
Proof with eauto using wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil, loc_transform_ident.
  intros * EnvTyp Binds StoreBinds Typ.
  epose proof (typing_var_implies_binds_typ _ _ _ _ _ Typ) as [D [Q [Binds2 [xSubD [WfD [QSubR1 PureR1]]]]]].
  unshelve epose proof ((proj1 (env_typing_inversion _ _ _ R _ _ EnvTyp Binds)) _)...
  unshelve epose proof (binds_unique _ _ _ _ _ Binds2 H _) as Eq...
  inversion Eq; subst...
Qed.

Lemma store_binds_frame_typ_sub : forall S E (x: atom) lx D Q C R,
  binds x lx E ->
  frame_typing S (exp_var_like x, E) (C # R) ->
  StoreImpl.binds lx (D # Q) S ->
  sub nil S Q R.
Proof with eauto using wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil, loc_transform_ident.
  intros * Binds Frame StoreBinds.
  epose proof (frame_typing_inversion _ _ _ _ Frame) as [Γ [T [T' [xTyp [EnvTyp [LocTransT Sub]]]]]].
  assert (WfCR: wf_typ nil S (C # R)) by applys frame_typing_regular Frame.
  assert (WfDQ: wf_typ nil S (D # Q)) by (eapply wf_typ_from_wf_store_ctx_nil; eauto).
  epose proof (proj2 (sub_capt_type _ _ _ _ Sub)) as [C0 [R0 Eq]]; subst.
  { exists C, R... }
  epose proof (loc_transform_capt_rev _ _ _ _ LocTransT) as [C' [R' [LocTransC' [LocTransR' Eq]]]]; subst.
  epose proof (store_binds_typ_sub _ _ _ _ _ _ _ _ _ EnvTyp Binds StoreBinds xTyp).
  inversion WfCR; subst.
  inversion WfDQ; subst.
  inversion Sub; subst.
  apply sub_transitivity with (Q := R0)...
  eapply sub_under_loc_transform...
Qed.

Lemma stores_preserves_typing : forall S SS x lx v E E' C1' R1',
  store_typing SS S ->
  binds x lx E ->
  stores lx (v, E') SS ->
  frame_typing S (exp_var_like x, E) (C1' # R1') ->
  exists C R,
    frame_typing S (v, E') (C # R) /\ sub nil S (cse_loc lx # R) (C1' # R1').
Proof with eauto using wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil, loc_transform_ident, subcapt_reflexivity, sub_reflexivity, loc_transform_cse_bound_fvar.
  intros * StoreTyp Binds Stores xFrameTyp.
  dependent induction xFrameTyp; intros; subst.
  unshelve epose proof (proj2 (store_typing_equivalent _ _ lx StoreTyp)) as [C [R StoreBinds]]...
  - unshelve epose proof (loc_transform_capt_rev _ _ _ _ H1) as [C1 [R1 [LocTransC1 [LocTransR1 Eq]]]]; subst.
    epose proof (store_typing_inversion _ _ _ _ _ _ _ StoreTyp StoreBinds Stores) as [FrameTyp Val].
    assert (WfCR: wf_typ nil S (C # R)) by applys frame_typing_regular FrameTyp.
    inversion WfCR; subst.
    exists C, R; split...
    eapply sub_under_loc_transform with (T1 := cse_fvar x # R) (T2 := C1 # R1) (E := E)...
    { apply loc_transform_equiv; split... }
    constructor...
    + epose proof (typing_var_implies_binds_typ _ _ _ _ _ H0) as [D [Q [Binds2 [xSubD [WfD [QSubR1 PureR1]]]]]]...
    + eapply store_binds_typ_sub...
    + assert (wf_typ Γ S (C1 # R1)) by applys typing_regular H0.
      inversion H2...
  - epose proof (proj2 (sub_capt_type _ _ _ _ H)) as [C0' [R0' Eq]]; subst.
    { exists C1', R1'... }
    epose proof (IHxFrameTyp _ _ _ _ StoreTyp Binds Stores ltac:(auto) eq_refl) as [C [R [FrameTyp' Sub]]].
    exists C, R; repeat split...
    eapply sub_transitivity with (Q := C0' # R0')...
Qed.

Lemma frame_typing_inv_app : forall S lx (f x : atom) E T,
  binds x lx E ->
  frame_typing S (f @ x, E) T ->
  exists C D Q U, frame_typing S (exp_var_like f, E) (C # (∀ (D # Q) U))
               /\ frame_typing S (exp_var_like x, E) (D # Q)
               /\ sub nil S (open_ct U (cse_loc lx)) T.
Proof with eauto.
  intros * Binds Frame.
  epose proof (frame_typing_inversion _ _ _ _ Frame) as [Γ [T1 [T1' [Typ [EnvTyp [LocTransT1 Sub]]]]]].
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
    eapply sub_transitivity with (Q := T1')...
    eapply sub_under_loc_transform...
Qed.

Lemma frame_typing_through_open_ve_typing : forall S E l (x y : atom) e T,
  y ∉ (fv_ct T `union`A fv_ve e `union`A fv_ce e) ->
  frame_typing S (open_ve e y (cse_fvar y), [(y, l)] ++ E) T ->
  binds x l E ->
  frame_typing S (open_ve e x (cse_fvar x), E) T.
Proof with eauto using wf_typ_from_wf_store_ctx_nil, sub_reflexivity, wf_typ_weaken_head.
  intros * NotIn eFrameTyp Binds.
  dependent induction eFrameTyp; subst.
  - inversion select (env_well_typed _ _ Γ); subst.
    inversion select (loc_transform _ _ _); subst.
    rewrite_env (nil ++ [(y, bind_typ (cse_loc l # R))] ++ Γ0) in H0.
    epose proof (typing_through_subst_ve _ _ _ _ _ _ _ x _ H0).
    simpl in H2.
    rewrite <- subst_ve_intro in H2...
    eapply typing_frame_transform with (U := subst_ct y (cse_fvar x) U)...
    + apply H2.
      unshelve epose proof ((proj1 (env_typing_inversion _ _ _ _ _ _ H6 Binds)) _) as xBinds...
      assert (wf_typ nil S (C # R)) as Wf...
      inversion Wf; subst...
      assert (wf_typ Γ0 S R). {
        rewrite_env (Γ0 ++ nil).
        eapply wf_typ_weaken_head...
      }
      eapply typing_sub with (R := cse_fvar x # R)...
      constructor...
    + eapply loc_transform_subst_bound_var...
      erewrite env_well_typed_preserves_dom...
  - eapply typing_frame_sub...
    eapply IHeFrameTyp with (y := y); simpl...
    enough (y `notin`A fv_ct U)...
    unshelve epose proof (wf_typ_notin_fv_ct y nil U S _ _)...
Qed.

Lemma frame_typing_weakening : forall S E1 E2 z l e T C R,
  StoreImpl.binds l (C # R) S ->
  z `notin`A dom E1 `union`A dom E2 ->
  frame_typing S (e, E1 ++ E2) T ->
  frame_typing S (e, E1 ++ [(z, l)] ++ E2) T.
Proof with eauto using wf_typ_notin_fv_ct, loc_transform_wf_nil, loc_transform_ident, sub_reflexivity.
  intros * Binds NotIn Frame.
  generalize dependent z.
  generalize dependent l.
  dependent induction Frame; subst; intros.
  - epose proof (env_well_typed_app _ _ _ _ H) as [Γ1 [Γ2 [Eq EnvTyp]]]; subst.
    epose proof (env_well_typed_weakening _ _ _ _ _ _ _ _ _ Binds H EnvTyp NotIn) as EnvTyp2.
    unshelve epose proof (loc_transform_weakening_fresh _ _ _ _ _ _ _ H1)...
    { assert (z `notin`A dom (E1 ++ E2))...
      rewrite (env_well_typed_preserves_dom _ _ _ H) in H2.
      assert (wf_typ (Γ1 ++ Γ2) S U)...
    }
    econstructor...
    eapply typing_weakening...
  - eapply typing_frame_sub...
Qed.


(* This lemma may be useless that I proved accidentally when I wanted to prove weakening *)
Lemma frame_typing_strengthening : forall S E1 E2 x l e T,
  x `notin`A fv_ve e `union`A fv_ce e ->
  frame_typing S (e, E1 ++ [(x, l)] ++ E2) T ->
  frame_typing S (e, E1 ++ E2) T.
Proof with eauto using wf_typ_from_wf_store_ctx_nil, sub_reflexivity, wf_typ_weaken_head.
  intros * NotIn Frame.
  dependent induction Frame; subst.
  - eapply loc_transform_mid in H1...
    epose proof (env_well_typed_app S E1 ((x, l) :: E2) Γ H) as [Γ1 [Γ2 [Eq EnvTyp2]]]; subst.
    inversion EnvTyp2; subst.
    unshelve epose proof (typing_loc_through_subst_ve _ _ _ _ _ _ _ _ _ H0 _)...
    rewrite subst_cb_map_fresh in H2...
    rewrite <- subst_ve_fresh in H2...
    epose proof (env_well_typed_strengthening _ _ _ _ _ _ _ _ H6 H).
    eapply typing_frame_transform...
    enough (x `notin`A fv_cctx (Γ1 ++ [(x, bind_typ (cse_loc l # R))] ++ Γ))...
    { intro In.
      assert (x `in`A fv_cctx Γ1 `union`A fv_cctx ([(x, bind_typ (cse_loc l # R))] ++ Γ))...
      epose proof ((proj1 (fv_cctx_app _ _ _)) H4)...
    }
    eapply runtime_ctx_no_fv_cctx...
  - eapply typing_frame_sub...
    eapply IHFrame; simpl...
Qed.


(* Lemma frame_typing_inv_abs : forall S lx e1 E T T0 C0 R0, *)
(*   frame_typing S (λ (T0) e1, E) T -> *)
(*   StoreImpl.binds lx (C0 # R0) S -> *)
(*   (* loc_transform E T0 T0' -> *) *)
(*   sub nil S (C0 # R0) T0 -> *)
(*   forall U1 U2 C9, sub nil S T (C9 # (∀ (U1) U2)) -> *)
(*      sub nil S U1 T0 /\ *)
(*   exists S2, exists L, forall x, x ∉ L -> *)
(*     frame_typing S (open_ve e1 x (cse_fvar x), [(x, lx)] ++ E) (open_ct S2 (cse_loc lx)). *)
(* Proof with simpl_env; eauto using sub_reflexivity, subcapt_reflexivity, runtime_ctx_no_type_bindings, wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil, loc_transform_ident,wf_typ_from_wf_store_ctx. *)
(*   intros * Frame StoreBinds SubT0 * Sub. *)
(*   inversion Frame; subst. *)
(*   rename select (env_well_typed _ _ _) into EnvTyp. *)
(*   rename select (typing _ _ _ _) into Typ. *)
(*   rename select (loc_transform _ _ T) into LocTransU. *)
(*   assert (WfT0 : wf_typ nil S T0) by applys sub_regular SubT0. *)
(*   unshelve epose proof (proj1 (sub_capt_type _ _ _ _ SubT0)) as [D [Q Eq]]; subst... *)
(*   unshelve epose proof (proj2 (sub_capt_type _ _ _ _ Sub)) as [C' [R Eq]]; subst... *)
(*   inversion Sub; subst. *)
(*   rename select (sub _ _ _ _) into Sub2. *)
(*   unshelve epose proof (sub_inv_arr _ _ _ _ _ _ Sub2) as [T1' [T2' [Eq [Sub3 [L Sub4]]]]]; subst. *)
(*   { unfold no_type_bindings. intros. intro... } *)
(*   epose proof (loc_transform_capt_rev _ _ _ _ LocTransU) as [C [Fun [LocTransC [LocTransFun Eq]]]]; subst. *)
(*   epose proof (loc_transform_fun_rev _ _ _ _ LocTransFun) as [T1 [T2 [LocTransT1 [LocTransT2 Eq']]]]; subst. *)
(*   unshelve epose proof (typing_inv_abs _ _ _ _ _ Typ T1 T2 C _) as [Sub5 [S2 [L' Ret]]]... *)
(*   split. *)
(*   { apply sub_transitivity with (Q := T1')... *)
(*     eapply sub_under_loc_transform... } *)
(*   epose proof (loc_transform_result S2 E) as [S2' LocTransS2]. *)
(*   exists S2', (L `union`A L' `union`A dom E). *)
(*   intros * Fr. *)
(*   destruct (Ret x ltac:(fsetdec)) as [e1Typ [WfS2 [S2SubT2 NotIn]]]. *)
(*   assert (x `notin`A dom Γ) as NotInE. *)
(*   { rewrite <- (env_well_typed_preserves_dom _ _ _ EnvTyp); fsetdec. } *)
(*   assert (EnvTyp2 : env_well_typed S ([(x, lx)] ++ E) ([(x, bind_typ (cse_loc lx # R0))] ++ Γ)) by (econstructor; eauto). *)
(*   econstructor. *)
(*   - apply EnvTyp2. *)
(*   - rewrite_env (nil ++ [(x, bind_typ (cse_loc lx # R0))] ++ Γ). *)
(*     eapply typing_narrowing_typ... *)
(*     assert (Wf: wf_typ nil S (C0 # R0))... *)
(*     inversion Wf; subst... *)
(*     inversion SubT0'; subst. *)
(*     admit. *)
(*     (* constructor... *) *)
(*     (* econstructor... *) *)
(*     (* rewrite_env (nil ++ Γ ++ nil). *) *)
(*     (* eapply sub_weakening... *) *)
(*   - eapply loc_transform_open_ct_bound_var... *)
(*     econstructor... *)
(*     (* constructor... *) *)
(*     rewrite <- subst_ct_fresh... *)
(* Qed. *)

(* Lemma frame_typing_inv_abs2 : forall S lx e1 E Γ T T' T0 C0 R0, *)
(*   (* frame_typing S (λ (T0) e1, E) T -> *) *)
(*   env_well_typed S E Γ -> *)
(*   typing Γ S (λ (T0) e1) T' -> *)
(*   loc_transform E T' T -> *)
(*   StoreImpl.binds lx (C0 # R0) S -> *)
(*   sub Γ S (C0 # R0) T0 -> *)
(*   forall U1 U2 C9, sub Γ S T (C9 # (∀ (U1) U2)) -> *)
(*      sub Γ S U1 T0 /\ *)
(*   exists S2, exists L, forall x, x ∉ L -> *)
(*     frame_typing S (open_ve e1 x (cse_fvar x), [(x, lx)] ++ E) (open_ct S2 (cse_loc lx)). *)
(* Proof with simpl_env; eauto using sub_reflexivity, subcapt_reflexivity, runtime_ctx_no_type_bindings, wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil, loc_transform_ident,wf_typ_from_wf_store_ctx. *)
(*   intros * EnvTyp Typ LocTrans StoreBinds SubT0 * Sub. *)
(*   (* inversion Frame; subst. *) *)
(*   (* rename select (env_well_typed _ _ _) into EnvTyp. *) *)
(*   (* rename select (typing _ _ _ _) into Typ. *) *)
(*   (* rename select (loc_transform _ _ _) into LocTrans. *) *)
(*   assert (WfT0 : wf_typ Γ S T0) by applys sub_regular SubT0. *)
(*   unshelve epose proof (proj1 (sub_capt_type _ _ _ _ SubT0)) as [D [Q Eq]]; subst... *)
(*   unshelve epose proof (proj2 (sub_capt_type _ _ _ _ Sub)) as [C' [R Eq]]; subst... *)
(*   inversion Sub; subst. *)
(*   rename select (sub _ _ _ _) into Sub2. *)
(*   unshelve epose proof (sub_inv_arr _ _ _ _ _ _ Sub2) as [T1' [T2' [Eq [Sub3 [L Sub4]]]]]; subst. *)
(*   { admit. } *)
(*   (* { unfold no_type_bindings. intros. intro... } *) *)
(*   epose proof (loc_transform_capt_rev _ _ _ _ LocTrans) as [C [Fun [LocTransC [LocTransFun Eq]]]]; subst. *)
(*   epose proof (loc_transform_fun_rev _ _ _ _ LocTransFun) as [T1 [T2 [LocTransT1 [LocTransT2 Eq']]]]; subst. *)
(*   unshelve epose proof (typing_inv_abs _ _ _ _ _ Typ T1 T2 C _) as [Sub5 [S2 [L' Ret]]]... *)
(*   split. *)
(*   { apply sub_transitivity with (Q := T1)... *)
(*   (*   rewrite_env (nil ++ Γ ++ nil). *) *)
(*   (*   eapply sub_weakening... *) *)
(*   (*   eapply sub_under_loc_transform... } *) *)
(*   epose proof (loc_transform_result S2 E) as [S2' LocTransS2]. *)
(*   exists S2', (L `union`A L' `union`A dom E). *)
(*   intros * Fr. *)
(*   destruct (Ret x ltac:(fsetdec)) as [e1Typ [WfS2 [S2SubT2 NotIn]]]. *)
(*   assert (x `notin`A dom Γ) as NotInE. *)
(*   { rewrite <- (env_well_typed_preserves_dom _ _ _ EnvTyp); fsetdec. } *)
(*   assert (EnvTyp2 : env_well_typed S ([(x, lx)] ++ E) ([(x, bind_typ (cse_loc lx # R0))] ++ Γ)) by (econstructor; eauto). *)
(*   econstructor. *)
(*   - apply EnvTyp2. *)
(*   - rewrite_env (nil ++ [(x, bind_typ (cse_loc lx # R0))] ++ Γ). *)
(*     eapply typing_narrowing_typ... *)
(*     assert (Wf: wf_typ Γ S (C0 # R0))... *)
(*     inversion Wf; subst... *)
(*     inversion SubT0; subst. *)
(*     constructor... *)
(*     (* rewrite_env (nil ++ Γ ++ nil). *) *)
(*     (* eapply sub_weakening... *) *)
(*     (* simpl_env... *) *)
(*   - eapply loc_transform_open_ct_bound_var... *)
(*     econstructor... *)
(*     (* constructor... *) *)
(*     rewrite <- subst_ct_fresh... *)
(* Qed. *)

(* TODO: Work in progress *)

Lemma frame_typing_inv_abs : forall S l e1 E C D D0 Q Q0 U T0,
  frame_typing S (λ (T0) e1, E) (C # (∀ (D # Q) U)) ->
  StoreImpl.binds l (D0 # Q0) S ->
  sub nil S Q0 Q ->
  exists L, forall x, x `notin`A L ->
    frame_typing S (open_ve e1 x (cse_fvar x), [(x, l)] ++ E) (open_ct U (cse_loc l)).
Proof with eauto using wf_typ_notin_fv_ct, wf_typ_from_wf_store_ctx_nil, loc_transform_ident, sub_reflexivity.
  intros * Frame StoreBinds Sub.
  generalize dependent l.
  generalize dependent Q0.
  generalize dependent D0.
  (* generalize dependent x. *)
  (* generalize dependent L. *)
  dependent induction Frame; subst; intros.
  - rename select (env_well_typed _ _ _) into EnvTyp.
    rename select (typing _ _ _ _) into Typ.
    rename select (loc_transform _ _ _) into LocTrans.
    epose proof (loc_transform_capt_rev _ _ _ _ LocTrans) as [C' [Fun [LocTransC' [LocTransFun Eq]]]]; subst.
    epose proof (loc_transform_fun_rev _ _ _ _ LocTransFun) as [T1 [U' [LocTransT1 [LocTransU Eq']]]]; subst.
    (* epose proof (loc_transform_capt_rev _ _ _ _ LocTransT1) as [D' [Q' [LocTransD' [LocTransQ' Eq'']]]]; subst. *)
    unshelve epose proof (typing_inv_abs _ _ _ _ _ Typ T1 U' C' _) as [Sub' [S2 [L' Ret]]]; subst.
    { apply sub_reflexivity... }
    exists (L' `union`A dom Γ `union`A fv_ct U').
    intros.
    eapply typing_frame_transform with (Γ := ([(x, bind_typ (cse_loc l # Q0))] ++ Γ)) (U := open_ct U' (cse_fvar x)).
    + econstructor...
    + epose proof (loc_transform_capt_rev _ _ _ _ LocTransT1) as [D' [Q' [LocTransD' [LocTransQ' Eq'']]]]; subst.
      epose proof (proj1 (sub_capt_type _ _ _ _ Sub')) as [C0 [R0 Eq]]; subst.
      { exists D', Q'... }
      assert (sub Γ S (cse_loc l # Q0) (D' # Q')) as SubDQ' by admit.
      (* { *)
      (*   constructor... *)
      (**)
      (*   - admit. *)
      (*   -  *)
      (* } *)
      specialize (Ret x ltac:(fsetdec)) as [e1Typ [WfS2 [S2SubU NotIn]]].
      eapply typing_sub with (R := open_ct S2 (cse_fvar x))...
      * rewrite_env (nil ++ [(x, bind_typ (C0 # R0))] ++ Γ) in e1Typ.
        epose proof (typing_narrowing_typ _ _ _ _ _ _ _ _ _ _ e1Typ); simpl in H0.
        apply H0...
        apply sub_transitivity with (Q := D' # Q')...
      * rewrite_env (nil ++ [(x, bind_typ (D' # Q'))] ++ Γ) in S2SubU.
        epose proof (sub_narrowing_typ _ _ _ _ _ _ _ _ _ _ S2SubU).
        simpl in H0.
        apply H0...
    + eapply loc_transform_open_ct_bound_var...
      econstructor...
      constructor...
      rewrite <- subst_ct_fresh...
      Admitted.
