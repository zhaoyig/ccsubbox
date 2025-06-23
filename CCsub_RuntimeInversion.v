Require Import Coq.Program.Equality.
Require Import LibTactics.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.
Require Import CCsub_Red.
(* Require Import CCsub_Precise. *)

Hint Constructors store_typing eval_typing state_typing : core.

(************************************************************************ *)
(** ** Properties of values *)

Lemma capture_prediction : forall Γ v E C R S,
  value (v, E) ->
  typing Γ S v (C # R) ->
  subcapt Γ S (exp_cv v) C.
Proof with subst; simpl; eauto.
  intros * Value Typ.
  forwards (WfS & WfCtx & Expr & WfTyp): typing_regular Typ.
  eremember (C # R) as T.
  assert (sub Γ S T (C # R)) by (rewrite HeqT; apply sub_reflexivity; eauto* ).
  clear HeqT.
  generalize dependent R.
  generalize dependent C.
  induction Typ; intros C0 R0 Sub; cbn [exp_cv]; try solve [ inversion Value ].
  - inversion WfTyp; subst.
    inversion Sub...
  - inversion WfTyp; subst.
    inversion Sub...
  - apply subcapt_bot.
    enough (WfC0R0 : wf_typ Γ S (C0 # R0)) by (inversion WfC0R0; auto).
    applys sub_regular Sub.
    apply sub_regular in Sub.
    destruct Sub as [_ [_ [_ WF_C0]]].
    inversion WF_C0; subst...
  - forwards: IHTyp...
    apply (sub_transitivity T)...
Qed.

Lemma values_have_precise_captures : forall Γ v E C R S,
  value (v, E) ->
  typing Γ S v (C # R) ->
  exists U, typing Γ S v (exp_cv v # U) /\
            sub Γ S (exp_cv v # U) (C # R).
Proof with simpl; eauto*.
  intros * Value Typ.
  assert (wf_cse Γ S (exp_cv v)) by eauto using typing_cv.
  assert (wf_ctx Γ S) by applys typing_regular Typ.
  assert (wf_store_ctx S) by applys typing_regular Typ.
  induction Typ; try solve [inversion Value; subst].
  - Case "typing_abs".
    exists (∀ (C0 # R0) T1).
    split...
    eapply sub_reflexivity...
    constructor...
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ _ (open_ve _ _ _)  _) into IH.
      forwards Typ: (IH x xIn).
      applys typing_regular Typ.
    + econstructor.
      1: eapply type_from_wf_typ...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ _ (open_ve _ _ _)  _) into IH.
      forwards Typ: (IH x xIn).
      eapply type_from_wf_typ...
  - Case "typing_tabs".
    exists (∀ [V] T1).
    split...
    eapply sub_reflexivity...
    constructor...
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ _ (open_te _ _) _) into IH.
      forwards Typ: (IH x xIn).
      applys typing_regular Typ.
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ _ (open_te _ _) _) into IH.
      forwards Typ: (IH x xIn).
      eapply type_from_wf_typ...
  - Case "typing_box".
    exists (□ (C0 # R0)).
    split...
    apply sub_reflexivity...
  - Case "typing_sub".
    forwards (U & HtypU & HsubS): IHTyp...
    exists U. split...
    eauto using (sub_transitivity R0).
Qed.

Definition no_type_bindings (Γ : ctx) : Prop :=
  forall X U, ~ binds X (bind_sub U) Γ.

Lemma well_typed_ctx_no_typ_bindings : forall S Γ E,
  env_well_typed S E Γ ->
  no_type_bindings Γ.
Proof with eauto*.
  intros * EnvTyp.
  dependent induction EnvTyp...
  - easy.
  - intros X U Binds.
    binds_cases Binds.
    rename select (binds _ (bind_sub _) _) into Binds.
    applys IHEnvTyp Binds.
Qed.

Lemma env_implies_value : forall S SS l v,
  store_typing SS S ->
  stores l v SS ->
  value v.
Proof with eauto*.
  intros * StoreTyp Stores.
  induction StoreTyp; inversion Stores; subst.
  destruct (l ==== l0); subst...
Qed.

(* Lemma eval_typing_sub : forall Γ S K R1 R2 T1 T2, *)
(*   sub Γ S R2 R1 -> *)
(*   eval_typing Γ S K R1 T1 -> *)
(*   sub Γ S T1 T2 -> *)
(*   eval_typing Γ S K R2 T2. *)
(* Proof with eauto*. *)
(*   intros * R2SubR1 EvalTyp T1SubT2. *)
(*   revert R2 T2 R2SubR1 T1SubT2. *)
(*   induction EvalTyp; intros R4 T2 R2subC1R1 C2R2subT2. *)
(*   - Case "typing_eval_nil". *)
(*     rename select (sub Γ S (C1 # R1) (C2 # R2)) into C1R1subC2R2. *)
(*     destruct (proj1 (sub_capt_type _ _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst. *)
(*     destruct (proj2 (sub_capt_type _ _ _ _ R2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst. *)
(*     apply typing_eval_nil... *)
(*     apply sub_transitivity with (Q := C1 # R1)... *)
(*     apply sub_transitivity with (Q := C2 # R2)... *)
(*   - Case "typing_eval_cons".   *)
(*     destruct (proj1 (sub_capt_type _ _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst. *)
(*     destruct (proj2 (sub_capt_type _ _ _ _ R2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst. *)
(*     apply typing_eval_cons with (L := L) (C2 := C2) (R2 := R2)... *)
(*     + intros x xNotIn. *)
(*       rewrite_nil_concat. *)
(*       eapply typing_narrowing_typ... *)
(*     + apply IHEvalTyp... *)
(*       apply sub_reflexivity... *)
(*       applys eval_typing_regular EvalTyp. *)
(* Qed. *)
(**)
(* Lemma eval_typing_weakening : forall Γ Δ Θ S E T U, *)
(*   eval_typing (Δ ++ Γ) S E T U -> *)
(*   wf_ctx (Δ ++ Θ ++ Γ) S -> *)
(*   eval_typing (Δ ++ Θ ++ Γ) S E T U. *)
(* Proof with eauto*. *)
(*   intros * EvalTyp WfCtx. *)
(*   induction EvalTyp. *)
(*   - Case "typing_eval_nil". *)
(*     apply typing_eval_nil... *)
(*     apply sub_weakening... *)
(*   - Case "typing_eval_cons". *)
(*     apply typing_eval_cons with (L := L `u`A dom (Δ ++ Θ ++ Γ)) (C2 := C2) (R2 := R2)... *)
(*     intros x xNotIn. *)
(*     rename select (forall x, x ∉ L -> typing _ _ _ _) into Typ. *)
(*     specialize (Typ x ltac:(fsetdec)). *)
(*     rewrite <- concat_assoc in Typ. *)
(*     apply typing_weakening with (Θ := Θ) in Typ. *)
(*     + apply Typ. *)
(*     + simpl_env. *)
(*       apply wf_ctx_typ... *)
(*       assert (WfCtx' : wf_ctx (([(x, bind_typ (C1 # R1))] ++ Δ) ++ Γ) S) by applys typing_regular Typ. *)
(*       inversion WfCtx'; subst. *)
(*       apply wf_typ_weakening... *)
(* Qed. *)
(**)
(* Lemma eval_typing_weakening_store : forall Γ S1 S2 S3 E T U, *)
(*   eval_typing Γ (S1 ++ S2) E T U -> *)
(*   wf_store_ctx (S1 ++ S3 ++ S2) -> *)
(*   eval_typing Γ (S1 ++ S3 ++ S2) E T U. *)
(* Proof with eauto*. *)
(*   intros * EvalTyp WfCtx. *)
(*   induction EvalTyp. *)
(*   - Case "typing_eval_nil". *)
(*     apply typing_eval_nil... *)
(*     apply sub_weakening_store... *)
(*   - Case "typing_eval_cons". *)
(*     apply typing_eval_cons with (L := L) (C2 := C2) (R2 := R2)... *)
(*     intros x xNotIn. *)
(*     specialize (H x xNotIn). *)
(*     apply typing_weakening_store with (S2 := S3) in H... *)
(* Qed. *)

Lemma store_typing_preserves_dom : forall SS S,
  store_typing SS S ->
  Store.dom SS = Store.dom S.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp...
  repeat rewrite dom_concat; simpl.
  rewrite IHStoreTyp...
Qed.

Lemma env_well_typed_preserves_dom : forall S E Γ,
  env_well_typed S E Γ ->
  dom E = dom Γ.
Proof with eauto*.
  intros * EnvTyp. dependent induction EnvTyp...
  simpl. rewrite IHEnvTyp...
Qed.

Lemma env_well_typed_store_ctx_wf : forall Γ S E,
  env_well_typed S E Γ ->
  wf_store_ctx S.
Proof with eauto.
  intros. dependent induction H...
Qed.

Lemma env_well_typed_ctx_wf : forall Γ S E,
  env_well_typed S E Γ ->
  wf_ctx Γ S.
Proof with eauto.
  intros. dependent induction H...
  constructor...
  eapply env_well_typed_store_ctx_wf in H.
  assert (WfCR : wf_typ Γ S (C # R)) by (eapply wf_typ_from_wf_store_ctx; eauto).
  inverts WfCR...
Qed.

(* Lemma fv_loc_transform_step : forall E T T2 x l Γ S, *)
(*   env_well_typed S ((x, l) :: E) Γ -> *)
(*   wf_typ Γ S T -> *)
(*   loc_transform_step ((x, l) :: E) T E T2 -> *)
(*   x `notin` (fv_ct T2 `union` fv_tt T2). *)
(* Proof with eauto. *)
(*   intros * EnvTyp WfTyp LocTrans. *)
(*   inverts EnvTyp; simpl in *. *)
(*   dependent induction LocTrans; simpl; eauto. *)
(*   rewrite_env (nil ++ [(x, bind_typ (cse_loc l # R))] ++ Γ0) in WfTyp. *)
(*   enough (wf_typ Γ0 S (subst_ct x (cse_loc l) T)) by *)
(*     (eauto using wf_typ_notin_fv_ct, wf_typ_fv_tt_in_ctx). *)
(*   epose proof (wf_typ_subst_cb _ _ _ _ _ _ _ WfTyp). *)
(*   simpl in H. *)
(*   epose proof (env_well_typed_ctx_wf _ _ _ H3). *)
(*   apply H... *)
(* Qed. *)

Lemma fv_loc_transform_nil : forall T1 T2 Γ S E,
  env_well_typed S E Γ ->
  wf_typ Γ S T1 ->
  loc_transform E T1 T2 ->
  wf_typ nil S T2.
Proof with eauto.
  intros * EnvTyp WfTyp LocTrans.
  generalize dependent Γ.
  dependent induction LocTrans; simpl in *; eauto; intros Γ EnvTyp WfTyp; subst.
  - inverts EnvTyp...
  - inverts EnvTyp.
    eapply IHLocTrans; eauto.
    rewrite_env (nil ++ [(x, bind_typ (cse_loc l # R))] ++ Γ0) in WfTyp.
    epose proof (wf_typ_subst_cb _ _ _ _ _ _ _ WfTyp).
    simpl in H.
    epose proof (env_well_typed_ctx_wf _ _ _ H3).
    apply H...
Qed.

Lemma frame_typing_regular : forall S e E T,
  frame_typing S (e, E) T ->
  wf_typ nil S T.
Proof with eauto.
  intros * FrameTyp.
  inverts FrameTyp...
  eapply fv_loc_transform_nil with (T1 := C # R)...
Qed.

Lemma typed_store_ctx_wf : forall S SS,
  store_typing SS S ->
  wf_store_ctx S.
Proof with eauto.
  intros. dependent induction H...
  constructor...
  eapply frame_typing_regular in H1...
Qed.

Lemma wf_store_ctx_ok : forall S,
  wf_store_ctx S ->
  Store.ok S.
Proof with eauto.
  intros. dependent induction H...
Qed.

Hint Resolve wf_store_ctx_ok typed_store_ctx_wf : core.

Lemma typed_store_ok : forall SS S,
  store_typing SS S ->
  Store.ok SS.
Proof with eauto.
  intros. dependent induction H...
  constructor...
  rewrite store_typing_preserves_dom with (S := S)...
Qed.

Lemma env_well_typed_weaken_store : forall Γ S1 S2 S3 E,
  env_well_typed (S1 ++ S3) E Γ ->
  wf_store_ctx (S1 ++ S2 ++ S3) ->
  env_well_typed (S1 ++ S2 ++ S3) E Γ.
Proof with eauto using wf_typ_weakening_store.
  intros * EnvTyp WfStore.
  dependent induction EnvTyp.
  - constructor...
  - econstructor...
Qed.

Lemma store_typing_equivalent : forall S SS l,
  store_typing SS S ->
  (exists C R, Store.binds l (C # R) S) <-> (exists v E, stores l (v, E) SS).
Proof with eauto.
  intros * StoreTyp.
  split; intros.
  {
    dependent induction StoreTyp.
    - destruct H as [C [R Binds]]. inversion Binds.
    - destruct H2 as [C' [R' Binds]].
      rewrite_env ([(l0, (C # R))] ++ S) in Binds.
      Store.binds_cases Binds; subst.
      + assert (exists C R, Store.binds l (C # R) S) by (exists C', R'; eauto).
        destruct (IHStoreTyp H3) as [v0 [E0 Stores]].
        exists v0, E0.
        apply Store.binds_tail with (F := [(l0, store (v, E))]) in Stores; simpl in *...
      + inversion H4; subst.
        exists v, E.
        rewrite_env ([(l, store (v, E))] ++ SS).
        apply Store.binds_head, Store.binds_singleton.
   }
  {
    dependent induction StoreTyp.
    - destruct H as [v [E Binds]]. inversion Binds.
    - destruct H2 as [v0 [E0 Binds]].
      rewrite_env ([(l0, store (v, E))] ++ SS) in Binds.
      unfold stores in Binds. Store.binds_cases Binds; subst.
      + assert (exists v E, stores l (v, E) SS) by (exists v0, E0; eauto).
        destruct (IHStoreTyp H3) as [C' [R' Stores]].
        exists C', R'.
        apply Store.binds_tail with (F := [(l0, (C # R))]) in Stores; simpl in *...
      + inversion H4; subst.
        exists C, R.
        rewrite_env ([(l, (C # R))] ++ S).
        apply Store.binds_head, Store.binds_singleton.
  }
Qed.

Lemma store_typing_inversion : forall S SS E l v U,
  store_typing SS S ->
  Store.binds l U S ->
  stores l (v, E) SS ->
  exists Γ C R, (typing Γ S v (C # R) /\ env_well_typed S E Γ /\ loc_transform E (C # R) U /\ value (v, E)).
Proof with eauto using typing_weakening_store, env_well_typed_weaken_store, wf_typ_weakening_store.
  intros * StoreTyp lBindsU lBindsv.
  dependent induction StoreTyp.
  inversion lBindsU.
  assert (WfStore : wf_store_ctx S) by applys typed_store_ctx_wf StoreTyp.
  assert (WfCR : wf_typ nil S (C # R)) by applys frame_typing_regular H0.
  rewrite_env ([(l0, (C # R))] ++ S) in lBindsU.
  Store.binds_cases lBindsU; subst.
  - rewrite_env ([(l0, store (v0, E0))] ++ SS) in lBindsv.
    unfold stores in lBindsv. Store.binds_cases lBindsv...
    + unshelve epose proof IHStoreTyp as [Γ0 [C0 [R0 [Typ [EnvTyp [WfU Val]]]]]]...
      assert (wf_store_ctx ([(l0, C # R)] ++ S)) by (constructor; eauto).
      exists Γ0, C0, R0; rewrite_env (nil ++ [(l0, C # R)] ++ S)...
      repeat split...
    + simpl in Fr; flsetdec.
  - rewrite_env ([(l, store (v0, E0))] ++ SS) in lBindsv.
    unfold stores in lBindsv. Store.binds_cases lBindsv...
    + simpl in Fr; flsetdec.
    + inversion select (store _ = store _); subst.
      assert (wf_store_ctx ([(l, C # R)] ++ S)) by (constructor; eauto).
      inverts H0.
      exists Γ, C0, R0; rewrite_env (nil ++ [(l, C # R)] ++ S).
      repeat split; auto.
      apply typing_weakening_store...
      apply env_well_typed_weaken_store...
Qed.

Lemma env_typing_equivalent : forall S E Γ x l,
  env_well_typed S E Γ ->
  binds x l E <-> (exists R, binds x (bind_typ (cse_loc l # R)) Γ).
Proof with eauto.
  intros * EnvTyp. dependent induction EnvTyp; split; intros.
  2: destruct H0 as [R H0].
  1,2: inversion H0.
  - rename select (binds _ _ _) into Binds.
    binds_cases Binds; subst...
    unshelve epose proof (proj1 IHEnvTyp) as [R0 Binds]...
  - destruct H1 as [R0 Binds].
    binds_cases Binds; subst...
    + unshelve epose proof (proj2 IHEnvTyp)...
    + inversion select (_ = _)...
Qed.

Lemma env_typing_inversion : forall S E Γ R x l,
  env_well_typed S E Γ ->
  binds x l E ->
  (exists C, Store.binds l (C # R) S) <-> binds x (bind_typ (cse_loc l # R)) Γ.
Proof with eauto.
  intros * EnvTyp Binds.
  assert (WfS : wf_store_ctx S) by (eapply env_well_typed_store_ctx_wf; eauto).
  assert (okS : Store.ok S) by (eapply wf_store_ctx_ok; eauto).
  assert (WfCtx : wf_ctx Γ S) by (eapply env_well_typed_ctx_wf; eauto).
  split; intros.
  {
    dependent induction EnvTyp.
    - inversion Binds.
    - binds_cases Binds; subst...
      destruct H1 as [C0 Binds].
      epose proof (Store.binds_unique _ _ _ _ _ okS H0 Binds).
      inversion select (_ = _); subst...
  }
  {
    dependent induction EnvTyp.
    - inversion Binds.
    - binds_cases Binds; subst.
      + apply IHEnvTyp...
        simpl in Fr, H1. inverts H1...
        destruct (x == x0); fsetdec.
      + rewrite_env (nil ++ [(x, bind_typ (cse_loc l0 # R0))] ++ Γ) in H1.
        apply binds_mid_eq in H1...
        inverts H1...
  }
Qed.

(* Lemma prec_typing_weakening_store : forall Γ e T S1 S2 S3, *)
(*   prec_typing Γ (S1 ++ S3) e T -> *)
(*   wf_store_ctx (S1 ++ S2 ++ S3) -> *)
(*   prec_typing Γ (S1 ++ S2 ++ S3) e T. *)
(* Proof with eauto using *)
(*   wf_typ_weakening_store, *)
(*   wf_cse_weakening_store, *)
(*   wf_ctx_weakening_store, *)
(*   sub_weakening_store, *)
(*   subcapt_weakening_store. *)
(*   intros * Typ. remember (S1 ++ S3). *)
(*   generalize dependent S1. *)
(*   induction Typ; intros S1 EQ Ok; subst... *)
(*   - pick fresh x and apply prec_typing_abs... *)
(*   - pick fresh x and apply prec_typing_let... *)
(*   - pick fresh x and apply prec_typing_tabs... *)
(* Qed. *)

(* Lemma prec_store_typing_inversion : forall SS S l v E U, *)
(*   prec_store_typing SS S -> *)
(*   Store.binds l U S -> *)
(*   stores l (v, E) SS -> *)
(*   exists Γ, (prec_typing Γ S v U /\ env_well_typed S E Γ /\ wf_typ nil S U /\ value(v, E)). *)
(* Proof with eauto using prec_typing_weakening_store, env_well_typed_weaken_store, wf_typ_weakening_store. *)
(*   intros * PStoreTyp lBindsU lBindsv. *)
(*   dependent induction PStoreTyp. *)
(*   inversion lBindsU. *)
(*   assert (StoreTyp : store_typing SS S) by (eapply prec_store_typing_implies_store_typing; eauto). *)
(*   assert (WfStore : wf_store_ctx S) by applys typed_store_ctx_wf StoreTyp. *)
(*   rewrite_env ([(l0, (C # R))] ++ S) in lBindsU. *)
(*   Store.binds_cases lBindsU; subst. *)
(*   - rewrite_env ([(l0, store (v0, E0))] ++ SS) in lBindsv. *)
(*     unfold stores in lBindsv. Store.binds_cases lBindsv... *)
(*     + destruct (IHPStoreTyp H4 H5) as [Γ0 [Typ [EnvTyp [WfU Val]]]]. *)
(*       assert (wf_store_ctx ([(l0, C # R)] ++ S)) by (constructor; eauto). *)
(*       exists Γ0; rewrite_env (nil ++ [(l0, C # R)] ++ S)... *)
(*       repeat split... *)
(*     + simpl in Fr; flsetdec. *)
(*   - rewrite_env ([(l, store (v0, E0))] ++ SS) in lBindsv. *)
(*     unfold stores in lBindsv. Store.binds_cases lBindsv... *)
(*     + simpl in Fr; flsetdec. *)
(*     + inversion H6; subst. *)
(*       assert (wf_store_ctx ([(l, C # R)] ++ S)) by (constructor; eauto). *)
(*       exists Γ; rewrite_env (nil ++ [(l, C # R)] ++ S). *)
(*       repeat split; auto. *)
(*       apply prec_typing_weakening_store... *)
(*       apply env_well_typed_weaken_store... *)
(*       apply wf_typ_weakening_store... *)
(* Qed. *)

Lemma val_env : forall E v,
  value (v, E) ->
  fv_ve v = dom E.
Proof with eauto.
  intros * Value.
  dependent induction Value; simpl; eauto.
Qed.

(* Lemma prec_typing_strengthen_var : forall Γ S (x x0 : atom) C R C1 R1, *)
(*   prec_typing ((x0, bind_typ (C1 # R1)) :: Γ) S x (C # R) -> *)
(*   x <> x0 -> *)
(*   prec_typing Γ S x (C # R). *)
(* Proof with eauto. *)
(*   intros * PTyp xNeq. *)
(*   dependent induction PTyp; simpl; eauto. *)
(*   rewrite_env ([(x0, bind_typ (C1 # R1))] ++ Γ) in H0. *)
(*   binds_cases H0; subst. *)
(*   eapply prec_typing_var... *)
(*   inverts H... *)
(* Qed. *)
(**)
(* Lemma prec_typing_values_have_precise_captures : forall Γ S v E C R, *)
(*   value (v, E) -> *)
(*   prec_typing Γ S v (C # R) -> *)
(*   C = exp_cv v. *)
(* Proof with eauto. *)
(*   intros * Value PTyp. *)
(*   dependent induction PTyp; simpl in *; try solve [inversion Value; subst]... *)
(* Qed. *)

(* Lemma stores_preserves_typing : forall SS Γ S E E0 (x : atom) l v C R, *)
(*   store_typing SS S -> *)
(*   env_well_typed S E Γ -> *)
(*   binds x l E -> *)
(*   stores l (v, E0) SS -> *)
(*   typing Γ S x (C # R) -> *)
(*   exists D Q Γ0, *)
(*     typing Γ0 S v (exp_cv v # Q) /\ *)
(*     binds x (bind_typ (D # Q)) Γ0 /\ *)
(*     subcapt Γ S (exp_cv v) D /\ *)
(*     sub Γ S Q R. *)
(* Proof with eauto. *)
(*   intros * StoreTyp EnvTyp Binds Stores xTyp. *)
(*   epose proof (store_typing_equivalent). *)
(*   epose proof (store_typing_inversion). *)

(* Lemma stores_preserves_typing : forall SS Γ S E E0 (x : atom) l v C R, *)
(*   prec_store_typing SS S -> *)
(*   env_well_typed S E Γ -> *)
(*   binds x l E -> *)
(*   stores l (v, E0) SS -> *)
(*   prec_typing Γ S x (C # R) -> *)
(*   exists Γ0, *)
(*     prec_typing Γ0 S v (exp_cv v # R) /\ *)
(*     env_well_typed S E0 Γ0. *)
(* Proof with eauto. *)
(*   intros * PStoreTyp EnvTyp Binds Stores xPTyp. *)
(*   assert (StoreTyp : store_typing SS S) by (eapply prec_store_typing_implies_store_typing; eauto). *)
(*   assert (xTyp : typing Γ S x (C # R)) by (eapply prec_typing_implies_typing; eauto). *)
(*   destruct (typing_var_implies_binds_typ _ _ _ _ _ xTyp) as [D [Q [Binds2 [Subcapt [Wf [Sub Pure]]]]]]. *)
(*   dependent induction xPTyp; simpl in *... *)
(*   epose proof (binds_unique _ _ _ _ H0 Binds2). *)
(*   inverts H1. *)
(*   epose proof ((proj2 (env_typing_inversion _ _ _ _ _ _ _ EnvTyp Binds)) Binds2) as lBinds. *)
(*   epose proof (prec_store_typing_inversion _ _ _ _ _ _ PStoreTyp lBinds Stores). *)
(*   destruct H1 as [Γ0 [PTyp [EnvTyp0 [WfU Val]]]]. *)
(*   epose proof (prec_typing_values_have_precise_captures _ _ _ _ _ _ Val PTyp); subst. *)
(*   exists Γ0... *)
(* Qed. *)
