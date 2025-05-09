Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.

Set Nested Proofs Allowed.

(************************************************************************ *)
(** ** Properties of values *)

Lemma capture_prediction : forall Γ v E C R,
  value (v, E) ->
  typing Γ v (C # R) ->
  subcapt Γ (exp_cv v) C.
Proof with subst; simpl; eauto.
  intros * Value Typ.
  forwards (WfCtx & Expr & WfTyp): typing_regular Typ.
  eremember (C # R) as T.
  assert (sub Γ T (C # R)) by (rewrite HeqT; apply sub_reflexivity; eauto* ).
  clear HeqT.
  generalize dependent R.
  generalize dependent C.
  induction Typ; intros C0 R0 Sub; cbn [exp_cv]; try solve [ inversion Value ].
  - inversion WfTyp; subst.
    inversion Sub...
  - inversion WfTyp; subst.
    inversion Sub...
  - apply subcapt_bot.
    enough (WfC0R0 : wf_typ Γ (C0 # R0)) by (inversion WfC0R0; auto).
    applys sub_regular Sub.
    apply sub_regular in Sub.
    destruct Sub as [_ [_ WF_C0]].
    inversion WF_C0; subst...
  - forwards: IHTyp...
    apply (sub_transitivity T)...
Qed.

Lemma values_have_precise_captures : forall Γ v E C R,
  value (v, E) ->
  typing Γ v (C # R) ->
  exists U, typing Γ v (exp_cv v # U) /\
            sub Γ (exp_cv v # U) (C # R).
Proof with simpl; eauto*.
  intros * Value Typ.
  assert (wf_cse Γ (exp_cv v)) by eauto using typing_cv.
  assert (wf_ctx Γ) by applys typing_regular Typ.
  induction Typ; try solve [inversion Value; subst].
  - Case "typing_abs".
    exists (∀ (C0 # R0) T1).
    split...
    eapply sub_reflexivity...
    constructor...
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ (open_ve _ _ _)  _) into IH.
      forwards Typ: (IH x xIn).
      applys typing_regular Typ.
    + econstructor.
      1: eapply type_from_wf_typ...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ (open_ve _ _ _)  _) into IH.
      forwards Typ: (IH x xIn).
      eapply type_from_wf_typ...
  - Case "typing_tabs".
    exists (∀ [V] T1).
    split...
    eapply sub_reflexivity...
    constructor...
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ (open_te _ _) _) into IH.
      forwards Typ: (IH x xIn).
      applys typing_regular Typ.
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> typing _ (open_te _ _) _) into IH.
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

(************************************************************************ *)
(** ** Other helpers *)

Lemma subst_te_fresh_exp_cv : forall Z R e,
  exp_cv e = exp_cv (subst_te Z R e).
Proof with eauto*.
  intros.
  induction e; simpl in *...
Qed.

(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q Γ Δ Z R T P,
  sub (Δ ++ [(Z, bind_sub Q)] ++ Γ) R T ->
  sub Γ P Q ->
  sub (map (subst_tb Z P) Δ ++ Γ) (subst_tt Z P R) (subst_tt Z P T).
Proof with simpl_env;
           eauto 4 using wf_typ_subst_tb,
                         wf_ctx_subst_tb,
                         wf_typ_weaken_head,
                         subst_tt_pure_type,
                         subcapt_through_subst_tt.
  intros * SsubT PsubQ.
  assert (PureQ : pure_type Q).
  { forwards (WfCtx & _ & _): sub_regular SsubT.
    eapply wf_ctx_tail in WfCtx.
    inversion WfCtx...
  }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ PsubQ) PureQ)).
  dependent induction SsubT.
  - Case "sub_refl_tvar".
    simpl.
    destruct (X == Z); apply sub_reflexivity...
    replace (typ_var X) with (subst_tt Z P X).
    2: simpl; destruct (X == Z); [exfalso; apply (n e) | reflexivity ].
    eapply wf_typ_subst_tb...
  - Case "sub_trans_tvar".
    assert (wf_ctx (Δ ++ [(Z, bind_sub Q)] ++ Γ)) as WfC by auto.
    apply binding_uniq_from_wf_ctx in WfC as FrZ.
    simpl.
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_transitivity Q)...
      * rewrite_nil_concat.
        apply sub_weakening...
      * rewrite (subst_tt_fresh Z P Q).
        2: {
          assert (wf_typ Γ Q) as HA by auto.
          lets: notin_fv_wf_typ Z Q HA.
          fsetdec.
        }
        binds_get H.
        apply ok_from_wf_ctx in WfC...
        inversion H1; subst.
        apply (IHSsubT Q)...
    + SCase "X <> Z".
      binds_cases H.
      * assert (binds X (bind_sub U) (map (subst_tb Z P) Δ ++ Γ)) by auto.
        apply (sub_trans_tvar U)...
        rewrite (subst_tt_fresh Z P U).
        2: {
          assert (wf_typ Γ U) as HA. {
            eapply wf_typ_from_binds_sub...
          }
          lets: notin_fv_wf_typ Z HA.
          fsetdec.
        }
        apply (IHSsubT Q)...
      * apply (sub_trans_tvar (subst_tt Z P U)); [auto | eapply IHSsubT]...
  - Case "sub_capt".
    simpl; apply sub_capt...
  - Case "sub_top".
    simpl; apply sub_top...
  - Case "sub_arr".
    simpl; pick fresh y and apply sub_arr...
    repeat rewrite subst_tt_open_ct_var...
    rewrite <- concat_assoc.
    replace ([(y, bind_typ (C2 # subst_tt Z P R2))] ++ map (subst_tb Z P) Δ)
       with (map (subst_tb Z P) ([(y, bind_typ (C2 # R2))] ++ Δ))
         by reflexivity.
    eapply H3...
  - Case "sub_all".
    simpl; pick fresh Y and apply sub_all...
    repeat rewrite subst_tt_open_tt_var...
    rewrite <- concat_assoc.
    replace ([(Y, bind_sub (subst_tt Z P R2))] ++ map (subst_tb Z P) Δ)
       with (map (subst_tb Z P) ([(Y, bind_sub R2)] ++ Δ))
         by reflexivity.
    eapply H2...
  - Case "sub_box".
    simpl; apply sub_box...
Qed.

Lemma sub_through_subst_ct : forall x CU U C Γ Δ R T,
  sub (Δ ++ [(x, bind_typ (CU # U))] ++ Γ) R T ->
  subcapt Γ C CU ->
  sub (map (subst_cb x C) Δ ++ Γ) (subst_ct x C R) (subst_ct x C T).
Proof with eauto using wf_ctx_subst_cb,
                       wf_cse_over_subst,
                       subcapt_through_subst_cse,
                       subst_ct_pure_type.
  intros * Sub Subcapt.
  remember (Δ ++ [(x, bind_typ (CU # U))] ++ Γ).
  generalize dependent Δ.
  induction Sub; intros Δ EQ; subst.
  - Case "sub_refl_tvar".
    apply sub_refl_tvar...
    inversion H0; subst...
    rename select (binds X _ _) into Binds.
    binds_cases Binds...
    apply wf_typ_var with (T := subst_ct x C T).
    replace (bind_sub (subst_ct x C T))
       with (subst_cb x C (bind_sub T))
         by reflexivity.
    apply binds_head, binds_map; assumption.
  - Case "sub_trans_tvar".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds.
    + apply sub_trans_tvar with (U := U0)...
      rewrite (subst_ct_fresh x C U0)...
      assert (WfCtx : wf_ctx (Δ ++ [(x, bind_typ (CU # U))] ++ Γ)) by (applys sub_regular Sub).
      apply wf_ctx_tail in WfCtx.
      inversion WfCtx; subst.
      assert (WfU0 : wf_typ Γ U0).
      { applys wf_typ_ctx_bind_sub... }
      pose proof (notin_fv_wf_typ Γ x U0 WfU0 ltac:(assumption)).
      fsetdec.
    + apply sub_trans_tvar with (U := subst_ct x C U0)...
  - Case "sub_capt".
    apply sub_capt...
  - Case "sub_top".
    apply sub_top...
    eapply wf_typ_subst_cb...
  - Case "sub_arr".
    pick fresh y and apply sub_arr...
    fold subst_ct.
    repeat rewrite subst_ct_open_ct_var...
    rewrite <- concat_assoc.
    replace ([(y, bind_typ (subst_cse x C C2 # subst_ct x C R2))] ++ map (subst_cb x C) Δ)
       with (map (subst_cb x C) ([(y, bind_typ (C2 # R2))] ++ Δ))
         by reflexivity.
    eauto.
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    fold subst_ct.
    repeat rewrite subst_ct_open_tt_var...
    rewrite <- concat_assoc.
    replace ([(Y, bind_sub (subst_ct x C R2))] ++ map (subst_cb x C) Δ)
       with (map (subst_cb x C) ([(Y, bind_sub R2)] ++ Δ))
         by reflexivity.
    eauto*.
  - Case "sub_box".
    apply sub_box.
    fold subst_ct.
    apply IHSub...
Qed.

Lemma wf_pretyp_from_wf_ctx_typ : forall x C P Γ,
  wf_ctx ([(x, bind_typ (C # P))] ++ Γ) ->
  wf_typ Γ (C # P).
Proof with eauto*.
  intros * WfCtx.
  inversion WfCtx; auto; subst.
Qed.

Hint Resolve wf_pretyp_from_wf_ctx_typ : core.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma typing_var_implies_binds_typ : forall Γ (x : atom) C R,
  typing Γ x (C # R) ->
  exists D Q, binds x (bind_typ (D # Q)) Γ
           /\ subcapt Γ (cse_fvar x) C
           /\ wf_cse Γ D
           /\ sub Γ Q R
           /\ pure_type R.
Proof with eauto using sub_reflexivity.
  intros * Typ.
  assert (WfT : wf_typ Γ (C # R)) by applys typing_regular Typ.
  eremember (C # R) as T.
  assert (Sub : sub Γ T (C # R)).
  { subst.
    apply sub_reflexivity; applys typing_regular Typ.
  }
  clear HeqT.
  generalize dependent Sub.
  generalize dependent R.
  generalize dependent C.
  dependent induction Typ; intros D Q Sub.
  - exists C, R.
    assert (WfCR : wf_typ Γ (C # R)).
    { destruct (wf_typ_ctx_bind_typ x (C # R) Γ ltac:(assumption) ltac:(assumption)) as [D' [Q' [Eq Wf]]]...
      inversion Eq...
    }
    assert (WfDQ : wf_typ Γ (D # Q)).
    { applys sub_regular Sub. }
    inversion WfCR; inversion WfDQ; subst...
    inversion Sub...
  - assert (WfR : wf_typ Γ R).
    { apply sub_regular in H... }
    assert (RsubDQ : sub Γ R (D # Q)).
    { apply sub_transitivity with (Q := T)... }
    destruct (IHTyp x ltac:(reflexivity) WfR D Q RsubDQ) as [C [R0 [Binds [WfD [WfC [RsubQ PureQ]]]]]].
    exists C, R0.
    repeat split...
Qed.

(*
Lemma typing_through_subst_ve : forall Γ Δ x T C R e (u : atom) S,
  typing (Δ ++ [(x, bind_typ (C # R))] ++ Γ) S e T ->
  typing Γ S u (C # R) ->
  typing (map (subst_cb x (cse_fvar u)) Δ ++ Γ) S (subst_ve x u (cse_fvar u) e) (subst_ct x (cse_fvar u) T).
Proof with eauto*.
  intros * Typ uTyp.
  forwards (WfStore & WfCtx & _ & WfT): typing_regular Typ.
  assert (WfCtx' : wf_ctx Γ S) by (repeat apply wf_ctx_tail in WfCtx; assumption).
  destruct (typing_var_implies_binds_typ _ _ _ _ _ uTyp) as [D [Q [Binds [usubC [WfD [QsubR PureR]]]]]].
  assert (PureQ : pure_type Q) by (applys sub_pure_type QsubR; eauto).
  assert (WfU : wf_cse Γ S (cse_fvar u))
    by (eapply wf_cse_from_binds; eauto).
  assert (WfCtxSubst : wf_ctx (map (subst_cb x (cse_fvar u)) Δ ++ Γ) S) by (eapply wf_ctx_subst_cb; eauto).
  assert (uNotInΔ : u ∉ dom Δ).
  { eapply tail_not_in_head...
    apply binds_In in Binds.
    simpl; fsetdec.
  }
  assert (xNotInΓ : x ∉ dom Γ) by (apply fresh_mid_tail with (F := Δ) (a := (bind_typ (C # R))); eauto).
  assert (xNotInΔ : x ∉ dom Δ) by (eapply fresh_mid_head; eauto).
  assert (xNotInQ : x ∉ fv_ct Q) by (eapply wf_typ_notin_fv_ct; eauto).
  assert (xNotInR : x ∉ fv_ct R) by (eapply wf_typ_notin_fv_ct; eauto).
  dependent induction Typ; simpl.
  - Case "typing_var".
    destruct (x0 == x); subst; try (exfalso; fsetdec).
    + SCase "x0 = x".
      rename select (binds x _ _) into Binds'.
      binds_cases Binds'.
      * exfalso; simpl in *; fsetdec.
      * inversion select (bind_typ _ = bind_typ _); subst.
        rewrite_nil_concat.
        eapply typing_weakening.
        2: assumption.
        apply typing_sub with (R := cse_fvar u # R); simpl in *...
        destruct (x == x); try fsetdec.
        inversion uTyp...
        apply sub_capt...
        -- rewrite <- subst_ct_fresh...
        -- rewrite <- subst_ct_fresh...
        -- rewrite <- subst_ct_fresh... apply sub_reflexivity...
      * rename select (binds x _ _) into Binds'.
        apply binds_In in Binds'.
        contradiction.
    + SCase "x0 <> x".
      rename select (binds x0 _ _) into Binds'.
      binds_cases Binds'; destruct (x == x0); subst; simpl; destruct (x0 == x0); try fsetdec.
      * destruct (x0 == x); destruct (x == x0); try fsetdec; simpl.
        eapply typing_var with (C := C0)...
        apply binds_tail...
        rewrite <- subst_ct_fresh...
        eapply wf_typ_notin_fv_ct with (Γ := Γ)...
        rename select (binds x0 _ _) into Binds'.
        destruct (wf_typ_ctx_bind_typ _ _ _ _ WfCtx' Binds') as [D0 [Q0 [Eq WfD0Q0]]]; inversion Eq; subst; clear Eq.
        inversion WfD0Q0; subst...
      * destruct (x0 == x); destruct (x == x0); try fsetdec; simpl.
        eapply typing_var with (C := subst_cse x (cse_fvar u) C0)...
        rename select (binds x0 _ _) into Binds'.
        replace (bind_typ (subst_cse x (cse_fvar u) C0 # subst_ct x (cse_fvar u) R0))
           with (subst_cb x (cse_fvar u) (bind_typ (C0 # R0)))
             by reflexivity.
        apply binds_head, binds_map, Binds'.
  - Case "typing_loc".
    apply typing_loc with (C := C0)...
    rewrite <- subst_ct_fresh. assumption.
    apply wf_typ_from_wf_store_ctx_nil in H0.
    inversion H0; subst.
    apply wf_typ_notin_fv_ct with (x := x) in H6.
    assumption. fsetdec. assumption.
  - Case "typing_abs".
    rewrite subst_cse_cv_commutes_with_susbt_ve.
    pick fresh y and apply typing_abs.
    + replace (subst_cse x (cse_fvar u) C0 # subst_ct x (cse_fvar u) R0)
         with (subst_ct x (cse_fvar u) (C0 # R0))
           by reflexivity.
      eapply wf_typ_subst_cb...
    + rename select (forall x0 : atom, x0 ∉ L -> typing _ S (open_ve _ _ _) (open_ct _ _)) into e1Typ.
      specialize (e1Typ y ltac:(clear - Fr; fsetdec)).
      assert (Neq : x <> y) by (clear - Fr; fsetdec).
      rewrite_env (map (subst_cb x (cse_fvar u)) ([(y, bind_typ (C0 # R0))] ++ Δ) ++ Γ).
      rewrite subst_ct_open_ct_var.
      2-3: auto.
      rewrite subst_ve_open_ve_var.
      2-3: auto.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH with (C1 := C) (R1 := R)...
      eapply wf_ctx_subst_cb...
      eapply cset_from_wf_cse...
  - Case "typing_app".
    assert (Iff : (if f == x then (var_like_var (var_f u)) else var_like_var (var_f f)) = var_like_var (var_f (if f == x then u else f)))
      by (destruct_if; reflexivity).
    rewrite Iff.
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      unfold open_ct.
      rewrite subst_ct_open_rec...
      simpl. simpl. destruct (x == x); try fsetdec...
      eapply typing_app.
      * rewrite <- Iff.
        eapply IHTyp1...
      * fold subst_ct.
        replace (subst_cse x (cse_fvar u) D # subst_ct x (cse_fvar u) Q)
           with (subst_ct x (cse_fvar u) (D # Q))
             by reflexivity.
        replace (exp_var_like u) with (subst_ve x u (cse_fvar u) x).
        2: simpl; destruct_if...
        eapply IHTyp2...
    + SCase "x0 <> x".
      rewrite <- subst_ct_open_ct_var...
      apply typing_app with (D := subst_cse x (cse_fvar u) D) (Q := subst_ct x (cse_fvar u) Q) (C := subst_cse x (cse_fvar u) C0) (T := subst_ct x (cse_fvar u) T)...
      * replace (subst_cse x (cse_fvar u) C0 # ∀ ((subst_cse x (cse_fvar u) D # subst_ct x (cse_fvar u) Q)) subst_ct x (cse_fvar u) T)
           with (subst_ct x (cse_fvar u) (C0 # ∀ (D # Q) T))
             by reflexivity.
        rewrite <- Iff.
        eapply IHTyp1...
      * replace (subst_cse x (cse_fvar u) D # subst_ct x (cse_fvar u) Q)
           with (subst_ct x (cse_fvar u) (D # Q))
             by reflexivity.
        erewrite subst_ve_fresh with (x := x) (u := u) (c := cse_fvar u) (e := x0).
        2: simpl; fsetdec.
        eapply IHTyp2...
  - Case "typing_let".
    pick fresh y and apply typing_let.
    + eapply IHTyp...
    + rewrite subst_ve_open_ve_var...
      fold subst_ct.
      replace ([(y, bind_typ (subst_cse x (cse_fvar u) C1 # subst_ct x (cse_fvar u) T1))] ++ map (subst_cb x (cse_fvar u)) Δ ++ Γ)
         with (map (subst_cb x (cse_fvar u)) ([(y, bind_typ (C1 # T1))] ++ Δ) ++ Γ)
           by reflexivity.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH...
      * apply wf_ctx_typ...
      * rewrite concat_assoc.
        apply wf_typ_weaken_head...
      * eapply wf_ctx_subst_cb...
        eapply wf_ctx_typ...
  - Case "typing_tabs".
    rewrite subst_cse_cv_commutes_with_susbt_ve.
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_subst_cb...
    + apply subst_ct_pure_type...
    + rename select (forall X : atom, X ∉ L -> typing _ _ (open_te _ _) (open_tt _ _)) into e1Typ.
      specialize (e1Typ Y ltac:(clear - Fr; fsetdec)).
      assert (Neq : x <> Y) by (clear - Fr; fsetdec).
      rewrite_env (map (subst_cb x (cse_fvar u)) ([(Y, bind_sub V)] ++ Δ) ++ Γ).
      rewrite subst_ve_open_te_var.
      2-3: auto.
      rewrite subst_ct_open_tt_var.
      2-3: auto.
      rename select (forall X : atom, X ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH...
      eapply wf_ctx_subst_cb...
  - Case "typing_tapp".
    assert (Ifx0 : (if x0 == x then var_like_var (var_f u) else var_like_var (var_f x0)) = (var_like_var (if x0 == x then var_f u else var_f x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    rewrite subst_ct_open_tt...
    2: eapply bind_typ_notin_fv_tt with (T' := C # R) (Γ := Δ ++ [(x, bind_typ (C # R))] ++ Γ)...
    assert (Ifx0' : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0'.
    eapply typing_tapp with (Q := subst_ct x (cse_fvar u) Q) (C := subst_cse x (cse_fvar u) C0) (x := (if x0 == x then u else x0)).
    + replace (subst_cse x (cse_fvar u) C # ∀ [subst_ct x (cse_fvar u) Q] subst_ct x (cse_fvar u) T)
         with (subst_ct x (cse_fvar u) (C # ∀ [Q] T))
           by reflexivity.
      rewrite <- Ifx0'.
      rewrite <- Ifx0.
      eapply IHTyp...
    + apply sub_through_subst_ct with (CU := C) (U := R)...
  - Case "typing_box".
    assert (Ifx0 : (if x0 == x then var_like_var (var_f u) else var_like_var (var_f x0)) = (var_like_var (if x0 == x then var_f u else var_f x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    assert (Ifx0' : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0'.
    eapply typing_box.
    + replace (subst_cse x (cse_fvar u) C0 # subst_ct x (cse_fvar u) R0)
         with (subst_ct x (cse_fvar u) (C0 # R0))
           by reflexivity.
      rewrite <- Ifx0'.
      rewrite <- Ifx0.
      eapply IHTyp...
    + apply (wf_cse_over_subst Γ Δ (C # R) x (cse_fvar u) C0)...
  - Case "typing_unbox".
    assert (Ifx0 : (if x0 == x then var_like_var (var_f u) else var_like_var (var_f x0)) = (var_like_var (if x0 == x then var_f u else var_f x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    assert (Ifx0' : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0'.
    apply typing_unbox.
    + replace ({} # (□ subst_cse x (cse_fvar u) C0 # subst_ct x (cse_fvar u) R0))
         with (subst_ct x (cse_fvar u) ({} # (□ C0 # R0))).
      2: {
        simpl.
        f_equal...
      }
      rewrite <- Ifx0'.
      rewrite <- Ifx0.
      eapply IHTyp...
    + eapply wf_cse_over_subst...
  - Case "typing_sub".
    Set Printing Coercions.
    apply typing_sub with (R := subst_ct x (cse_fvar u) R0).
    + eapply IHTyp...
    + apply sub_through_subst_ct with (CU := C) (U := R)...
Qed.
*)

Lemma wf_typ_free_in_ctx : forall x Γ T,
  wf_typ Γ T ->
  x ∉ dom Γ ->
  x ∉ fv_tt T.
Proof with eauto.
  intros * WfTyp Dom.
  dependent induction WfTyp; simpl in *...
  - apply binds_In in H.
    fsetdec.
  - pick fresh y for (L `u`A dom Γ `u`A {x}A).
    specialize (H0 y ltac:(fsetdec) ltac:(fsetdec)).
    apply notin_fv_tt_open_ct in H0.
    specialize (IHWfTyp Dom).
    fsetdec.
  - pick fresh y for (L `u`A dom Γ `u`A {x}A).
    specialize (H1 y ltac:(fsetdec) ltac:(fsetdec)).
    apply notin_fv_tt_open_tt in H1.
    specialize (IHWfTyp Dom).
    fsetdec.
Qed.

Lemma pure_wf_typ_no_fv_tt : forall x T,
  wf_typ nil T ->
  x ∉ fv_tt T.
Proof with eauto.
  intros * Wf.
  apply wf_typ_free_in_ctx with (Γ := nil)...
Qed.

Lemma typing_through_subst_te : forall Q Γ Δ Z e T P,
  typing (Δ ++ [(Z, bind_sub Q)] ++ Γ) e T ->
  sub Γ P Q ->
  typing (map (subst_tb Z P) Δ ++ Γ) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 4 using wf_ctx_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt,
                         wf_typ_from_binds_typ,
                         wf_typ_ignores_sub_bindings,
                         wf_typ_ignores_typ_bindings.
  intros * Typ PsubQ.
  assert (WfCtx : wf_ctx (Δ ++ [(Z, bind_sub Q)] ++ Γ)) by applys typing_regular Typ.
  assert (PureP : pure_type P).
  { applys sub_pure_type PsubQ.
    apply wf_ctx_tail in WfCtx.
    inversion WfCtx...
  }
  assert (ZNotInDomΓ : Z ∉ dom Γ).
  { eapply fresh_mid_tail, ok_from_wf_ctx.
    applys typing_regular Typ.
  }
  remember (Δ ++ [(Z, bind_sub Q)] ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ; subst;
    simpl subst_te in *; simpl subst_tt in *.
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds.
    + SCase "x ∈ dom Γ".
      rewrite <- subst_tt_fresh.
      * apply typing_var with (C := C)...
      * apply notin_fv_wf_typ with (Γ := Γ)...
        apply wf_typ_from_binds_typ in H1.
        inversion H1; subst...
        applys sub_regular PsubQ.
    + SCase "x ∈ dom Δ".
      apply typing_var with (C := C)...
      replace (bind_typ (C # subst_tt Z P R))
         with (subst_tb Z P (bind_typ (C # R)))
           by reflexivity.
      apply binds_head, binds_map.
      assumption.
  - Case "typing_abs".
    replace (exp_cv e1)
       with (exp_cv (subst_te Z P e1))
         by (symmetry; apply subst_te_fresh_exp_cv).
    pick fresh x and apply typing_abs.
    + replace (C # subst_tt Z P R)
         with (subst_tt Z P (C # R))
           by reflexivity.
      eapply wf_typ_subst_tb...
    + rewrite subst_tt_open_ct_var...
      rewrite subst_te_open_ve_var...
      rewrite_env (map (subst_tb Z P) ([(x, bind_typ (C # R))] ++ Δ) ++ Γ).
      apply H1.
      clear - Fr; fsetdec.
      apply wf_ctx_typ...
      reflexivity.
  - Case "typing_app".
    assert (Z <> x).
    { destruct (typing_var_implies_binds_typ _ _ _ _ Typ2) as [C' [R' [Binds _]]].
      binds_cases Binds; simpl_env in *...
      assert (Z ∉ dom Δ) by (eapply fresh_mid_head; eauto* ).
      apply binds_In in H0.
      fsetdec.
    }
    simpl.
    replace (subst_tt Z P (open_ct T (cse_fvar x)))
       with (open_ct (subst_tt Z P T) (cse_fvar x))
         by (apply open_ct_subst_tt; eauto* )...
    eapply typing_app...
    - Case "typing_let".
      pick fresh y and apply typing_let...
      rewrite <- subst_te_open_ve...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ (C1 # T1))] ++ Δ) ++ Γ).
      apply H0.
      clear - Fr; fsetdec.
      2: reflexivity.
      assert (WfC1T1 : wf_typ (Δ ++ [(Z, bind_sub Q)] ++ Γ) (C1 # T1)) by applys typing_regular Typ.
      apply wf_ctx_typ...
  - Case "typing_tabs".
    replace (exp_cv e1)
       with (exp_cv (subst_te Z P e1))
         by (symmetry; apply subst_te_fresh_exp_cv).
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_subst_tb...
    + apply subst_tt_pure_type...
    + rewrite subst_te_open_te_var...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ Δ) ++ Γ).
      apply H2.
      clear - Fr; fsetdec.
      2: reflexivity.
      apply wf_ctx_sub...
  - Case "typing_tapp".
    rewrite subst_tt_open_tt...
  - Case "typing_box".
    apply typing_box...
    assert (WfCR : wf_typ (Δ ++ [(Z, bind_sub Q)] ++ Γ) (C # R)).
    { applys typing_regular Typ. }
    assert (WfC : wf_cse (Δ ++ [(Z, bind_sub Q)] ++ Γ) C).
    { inversion WfCR... }
    apply (wf_cse_subst_tb _ _ Q Z P C)...
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cse_subst_tb...
  - Case "typing_sub".
    eapply typing_sub...
Qed.

(*
Lemma typing_through_open_ve_typing : forall Γ S (x y : atom) U e T,
  y ∉ (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  typing ([(y, bind_typ U)] ++ Γ) S (open_ve e y (cse_fvar y)) T ->
  typing Γ S x U ->
  typing Γ S (open_ve e x (cse_fvar x)) T.
Proof with eauto*.
  intros * NotIn Typ xTyp.
  assert (WfCtx : wf_ctx ([(y, bind_typ U)] ++ Γ) S) by applys typing_regular Typ.
  inversion WfCtx; subst.
  destruct (typing_var_implies_binds_typ _ _ _ _ S xTyp) as [D [Q [Binds [xsubC [WfD [QsubR PureR]]]]]].
  assert (Neq : x <> y).
  { enough (x ∈ dom Γ) by fsetdec.
    eapply binds_In, Binds.
  }
  rewrite_env (map (subst_cb y (cse_fvar x)) ∅ ++ Γ).
  replace (open_ve e x (cse_fvar x))
     with (subst_ve y x (cse_fvar x) (open_ve e y (cse_fvar y)))
       by (rewrite <- subst_ve_intro; auto).
  replace T
     with (subst_ct y (cse_fvar x) T)
       by (rewrite <- subst_ct_fresh; auto).
  eapply typing_through_subst_ve with (C := cse_fvar x) (R := Q).
  - eapply typing_narrowing_typ with (D := C) (Q := R)...
    apply sub_capt...
    applys sub_pure_type QsubR...
  - eapply typing_var...
Qed.

Lemma typing_through_open_ve_typing_open : forall Γ S (x y : atom) U e T,
  y ∉ (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  typing ([(y, bind_typ U)] ++ Γ) S (open_ve e y (cse_fvar y)) (open_ct T (cse_fvar y)) ->
  typing Γ S x U ->
  typing Γ S (open_ve e x (cse_fvar x)) (open_ct T (cse_fvar x)).
Proof with eauto*.
  intros * NotIn Typ xTyp.
  assert (WfCtx : wf_ctx ([(y, bind_typ U)] ++ Γ) S) by applys typing_regular Typ.
  inversion WfCtx; subst.
  destruct (typing_var_implies_binds_typ _ _ _ _ _ xTyp) as [D [Q [Binds [xsubC [WfD [QsubR PureR]]]]]].
  assert (Neq : x <> y).
  { enough (x ∈ dom Γ) by fsetdec.
    eapply binds_In, Binds.
  }
  rewrite_env (map (subst_cb y (cse_fvar x)) ∅ ++ Γ).
  replace (open_ve e x (cse_fvar x))
     with (subst_ve y x (cse_fvar x) (open_ve e y (cse_fvar y)))
       by (rewrite <- subst_ve_intro; auto).
  replace (open_ct T (cse_fvar x))
     with (subst_ct y (cse_fvar x) (open_ct T (cse_fvar y)))
       by (rewrite <- subst_ct_intro; auto).
  eapply typing_through_subst_ve with (C := cse_fvar x) (R := Q).
  - eapply typing_narrowing_typ with (D := C) (Q := R)...
    apply sub_capt...
    applys sub_pure_type QsubR...
  - eapply typing_var...
Qed.
 *)

Lemma typing_through_open_te : forall Γ (Y : atom) e T P Q,
  Y ∉ (fv_tt T `u`A fv_ct T `u`A fv_te e `u`A fv_ce e) ->
  typing ([(Y, bind_sub Q)] ++ Γ) (open_te e Y) (open_tt T Y) ->
  sub Γ P Q ->
  typing Γ (open_te e P) (open_tt T P).
Proof with eauto*.
  intros * NotIn Typ Sub.
  rewrite_env (map (subst_tb Y P) ∅ ++ Γ).
  replace (open_te e P)
     with (subst_te Y P (open_te e Y))
     by (symmetry; apply subst_te_intro; clear - NotIn; fsetdec).
  replace (open_tt T P)
     with (subst_tt Y P (open_tt T Y))
     by (symmetry; apply subst_tt_intro; clear - NotIn; fsetdec).
  apply typing_through_subst_te with (Q := Q)...
Qed.
