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
Require Import CCsub_FrameTypingInversion.

(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

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
    assert (sub nil S Q0 Q) by (eapply store_binds_frame_typ_sub with (x := y); eauto).
    econstructor...
    pick fresh x0.
    eapply frame_typing_through_open_ve_typing with (y := x0)...
    eapply typing_frame_sub with (U := open_ct U0 (cse_loc ly))...
    rewrite_env ([(x0, ly)] ++ [(z, ly)] ++ E').
    eapply frame_typing_weakening...
    (* TODO: frame_typing_inv_abs*)
Admitted.

(*
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
*)
