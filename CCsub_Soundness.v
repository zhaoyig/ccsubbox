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
  frame_typing S (exp_var x, E) (C # R) ->
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
  frame_typing S (exp_var x, E) (C1' # R1') ->
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
  exists C D Q U, frame_typing S (exp_var f, E) (C # (∀ (D # Q) U))
               /\ frame_typing S (exp_var x, E) (D # Q)
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

(* Inductive loc_typing : store_ctx -> loc -> typ -> Prop := *)
(*   | typing_loc : forall S l T U, *)
(*       wf_store_ctx S -> *)
(*       StoreImpl.binds l U S -> *)
(*       sub nil S U T -> *)
(*       loc_typing S l T. *)



(* TODO: Switch old proof to 8.20. add the new reduction semantics there and hope for the best *)

Lemma frame_typing_through_open_ve_typing_open : forall S E ly (x y : atom) U e T,
  y ∉ (fv_ct T `union`A fv_ve e `union`A fv_ce e) ->
  StoreImpl.binds ly U S ->
  frame_typing S (open_ve e y (cse_fvar y), [(y, ly)] ++ E) T ->
  frame_typing S (exp_var x, E) U ->
  frame_typing S (open_ve e x (cse_fvar x), E) T.
Proof with eauto.
  intros * NotIn LocBinds eFrameTyp xFrameTyp.
  epose proof (frame_typing_inversion _ _ _ _ xFrameTyp) as [Γ [T1 [T1' [Typ [EnvTyp [LocTransT1 Sub]]]]]].
  epose proof (frame_typing_inversion _ _ _ _ eFrameTyp) as [Γ' [T2 [T2' [eTyp [EnvTyp' [LocTransT2 Sub']]]]]].
  inversion LocTransT2; subst.
  apply typing_frame_sub with (U := T2')...
  inversion EnvTyp'; subst.
  (* epose proof (proj1 (env_typing_equivalent _ _ _ _ _ EnvTyp)) as [R2 Binds']... *)
  eapply typing_frame_transform with (Γ := Γ0)...
  eapply typing_through_open_ve_typing with (y := y).
(*   - admit. *)
(*   - admit. *)
(*   -  *)
(*    *)

Lemma preservation : forall Σ Σ' V,
  state_typing Σ V ->
  red Σ Σ' ->
  state_typing Σ' V.
Proof with eauto.
  intros * [S E SS K C1 R1 C2 R2 e StoreTyp EvalTyp FrameTyp] Red.
  (* inversion FrameTyp; subst. *)
  (* rename select (env_well_typed _ _ _) into EnvTyp. *)
  (* assert (WfC1R1 : wf_typ nil S (C1 # R1)) by applys frame_typing_regular FrameTyp. *)
  (* rename select (typing _ _ _ _) into Typ. *)
  dependent induction Red; intros.
  - (* Case "red_app". *)
    epose proof (frame_typing_inv_app _ _ _ _ _ _ H0 FrameTyp) as [C9 [D [Q [U0 [xTyp [yTyp USubC1R1]]]]]].
    epose proof (stores_preserves_typing _ _ _ _ _ _ _ _ _ StoreTyp H H1 xTyp) as [C0 [R0 [FrameTyp' Sub]]].
    destruct v as [v E''].
    epose proof (proj2 (store_typing_equivalent _ _ _ StoreTyp)) as [D0 [Q0 StoreBindsY]]...
    econstructor...
    assert (exists (S2 : typ) (L : atoms), forall x : atom, x ∉ L -> 
      frame_typing S (open_ve e1 x (cse_fvar x), [(x, ly)] ++ E') (open_ct S2 (cse_loc ly))). {
    inversion FrameTyp'; subst.
    epose proof (frame_typing_inv_abs _ _ _ _ _ _ _ _ _ _ H6 H8 H10 StoreBindsY).
    epose proof (loc_transform_capt_rev _ _ _ _ H10) as [Cu [Ru [LocTransCu [LocTransRu Eq]]]]; subst.
    inversion Sub; subst.
    unshelve epose proof (sub_inv_arr _ _ _ _ _ _ H14) as [U1 [U2 [Eq' [SubU1 _]]]]; subst.
    { unfold no_type_bindings. intros. intro... }
    epose proof (loc_transform_fun_rev _ _ _ _ LocTransRu) as [U1' [U2' [LocTransU1 [LocTransU2 Eq']]]]; subst.
    unshelve epose proof (typing_inv_abs _ _ _ _ _ H8 (D0 # Q0) U2' Cu _) as [a b]...
    admit.

              
    }
    (* destruct (typing_inv_app _ _ _ _ _ Typ) as [C9 [D [Q [U0 [xTyp [yTyp USubC1R1]]]]]]. *)
    (* epose proof (loc_transform_result ((∀ ((D # Q)) U0)) E) as [TFun LocTransDQ]. *)
    (* epose proof (loc_transform_fun _ _ _ _ _ LocTransDQ) as [D' [Q' [U' [LocTransD [LocTransQ [LocTransU Eq'']]]]]]; subst... *)
    (* epose proof (loc_transform_cse_result C9 E) as [C9' LocTransC9]. *)
    (* assert (frame_typing S (exp_var x, E) (C9' # (∀ ((D' # Q')) U'))). { *)
    (*   econstructor... *)
    (*   eapply (proj2 (loc_transform_equiv _ _ _ _ _))... *)
    (*   admit. *)
    (* } *)
    destruct ((proj2 (store_typing_equivalent _ _ lx StoreTyp))) as [C0 [R0 Binds]].
    eexists...
    assert (frame_typing S (λ (T) e1, E') (C0 # R0)). {
      epose proof (store_typing_inversion _ _ _ _ _ _ StoreTyp Binds H1) as [Γ0 [T0 [vTyp [EnvTyp' [LocTransT0 Val]]]]].
      econstructor...
    }
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
      apply env_cons with (C := D0)...
      rewrite <- (env_well_typed_preserves_dom _ _ _ EnvTyp2)...
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
