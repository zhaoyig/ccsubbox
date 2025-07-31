Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.

Set Nested Proofs Allowed.

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

Lemma sub_through_subst_tt : forall Q Γ Δ S Z R T P,
  sub (Δ ++ [(Z, bind_sub Q)] ++ Γ) S R T ->
  sub Γ S P Q ->
  sub (map (subst_tb Z P) Δ ++ Γ) S (subst_tt Z P R) (subst_tt Z P T).
Proof with simpl_env;
           eauto 4 using wf_typ_subst_tb,
                         wf_ctx_subst_tb,
                         wf_typ_weaken_head,
                         subst_tt_pure_type,
                         subcapt_through_subst_tt.
  intros * SsubT PsubQ.
  assert (PureQ : pure_type Q).
  { forwards (_ & WfCtx & _ & _): sub_regular SsubT.
    eapply wf_ctx_tail in WfCtx.
    inversion WfCtx...
  }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ _ PsubQ) PureQ)).
  dependent induction SsubT.
  - Case "sub_refl_tvar".
    simpl.
    destruct (X == Z); apply sub_reflexivity...
    replace (typ_var X) with (subst_tt Z P X).
    2: simpl; destruct (X == Z); [exfalso; apply (n e) | reflexivity ].
    eapply wf_typ_subst_tb...
  - Case "sub_trans_tvar".
    assert (wf_ctx (Δ ++ [(Z, bind_sub Q)] ++ Γ) S) as WfC by auto.
    apply binding_uniq_from_wf_ctx in WfC as FrZ.
    simpl.
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_transitivity Q)...
      * rewrite_nil_concat.
        apply sub_weakening...
      * rewrite (subst_tt_fresh Z P Q).
        2: {
          assert (wf_typ Γ S Q) as HA by auto.
          lets: notin_fv_wf_typ Z Q HA.
          fsetdec.
        }
        analyze_binds_uniq H...
        apply uniq_from_wf_ctx in WfC...
        inversion BindsTacVal; subst.
        apply (IHSsubT Q)...
    + SCase "X <> Z".
      analyze_binds_uniq H...
      * apply (sub_trans_tvar (subst_tt Z P U)); [auto | eapply IHSsubT]...
      * assert (binds X (bind_sub U) (map (subst_tb Z P) Δ ++ Γ)) by auto.
        apply (sub_trans_tvar U)...
        rewrite (subst_tt_fresh Z P U).
        2: {
          assert (wf_typ Γ S U) as HA. {
            eapply wf_typ_from_binds_sub...
          }
          lets: notin_fv_wf_typ Z HA.
          fsetdec.
        }
        apply (IHSsubT Q)...
  - Case "sub_capt".
    simpl; apply sub_capt...
  - Case "sub_top".
    simpl; apply sub_top...
  - Case "sub_arr".
    simpl; pick fresh y and apply sub_arr...
    repeat rewrite subst_tt_open_ct_var...
    rewrite <- app_assoc.
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ (C2 # R2))] ++ Δ) ++ Γ).
    eapply H3...
  - Case "sub_all".
    simpl; pick fresh Y and apply sub_all...
    repeat rewrite subst_tt_open_tt_var...
    rewrite <- app_assoc.
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub R2)] ++ Δ) ++ Γ).
    eapply H2...
  - Case "sub_box".
    simpl; apply sub_box...
Qed.

Lemma sub_through_subst_ct : forall x CU U C Γ Δ R T S,
  sub (Δ ++ [(x, bind_typ (CU # U))] ++ Γ) S R T ->
  subcapt Γ S C CU ->
  sub (map (subst_cb x C) Δ ++ Γ) S (subst_ct x C R) (subst_ct x C T).
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
    analyze_binds_uniq Binds...
    apply wf_typ_var with (T := subst_ct x C T).
    replace (bind_sub (subst_ct x C T))
       with (subst_cb x C (bind_sub T))
         by reflexivity.
    apply binds_app_2, binds_map; assumption.
  - Case "sub_trans_tvar".
    rename select (binds _ _ _) into Binds.
    analyze_binds_uniq Binds...
    + apply sub_trans_tvar with (U := subst_ct x C U0)...
    + apply sub_trans_tvar with (U := U0)...
      rewrite (subst_ct_fresh x C U0)...
      assert (WfCtx : wf_ctx (Δ ++ [(x, bind_typ (CU # U))] ++ Γ) S) by (applys sub_regular Sub).
      apply wf_ctx_tail in WfCtx.
      inversion WfCtx; subst.
      assert (WfU0 : wf_typ Γ S U0).
      { applys wf_typ_ctx_bind_sub... }
      pose proof (notin_fv_wf_typ Γ x U0 S WfU0 ltac:(assumption)).
      fsetdec.
  - Case "sub_capt".
    apply sub_capt...
  - Case "sub_top".
    apply sub_top...
    eapply wf_typ_subst_cb...
  - Case "sub_arr".
    pick fresh y and apply sub_arr...
    fold subst_ct.
    repeat rewrite subst_ct_open_ct_var...
    rewrite <- app_assoc.
    replace ([(y, bind_typ (subst_cse x C C2 # subst_ct x C R2))] ++ map (subst_cb x C) Δ)
       with (map (subst_cb x C) ([(y, bind_typ (C2 # R2))] ++ Δ))
         by reflexivity.
    eauto.
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    fold subst_ct.
    repeat rewrite subst_ct_open_tt_var...
    rewrite <- app_assoc.
    replace ([(Y, bind_sub (subst_ct x C R2))] ++ map (subst_cb x C) Δ)
       with (map (subst_cb x C) ([(Y, bind_sub R2)] ++ Δ))
         by reflexivity.
    eauto*.
  - Case "sub_box".
    apply sub_box.
    fold subst_ct.
    apply IHSub...
Qed.

Lemma wf_pretyp_from_wf_ctx_typ : forall x C P Γ S,
  wf_ctx ([(x, bind_typ (C # P))] ++ Γ) S ->
  wf_typ Γ S (C # P).
Proof with eauto*.
  intros * WfCtx.
  inversion WfCtx; auto; subst.
Qed.

Hint Resolve wf_pretyp_from_wf_ctx_typ : core.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma typing_var_implies_binds_typ : forall Γ (x : atom) C R S,
  typing Γ S x (C # R) ->
  exists D Q, binds x (bind_typ (D # Q)) Γ
           /\ subcapt Γ S (cse_fvar x) C
           /\ wf_cse Γ S D
           /\ sub Γ S Q R
           /\ pure_type R.
Proof with eauto using sub_reflexivity.
  intros * Typ.
  assert (WfT : wf_typ Γ S (C # R)) by applys typing_regular Typ.
  eremember (C # R) as T.
  assert (Sub : sub Γ S T (C # R)).
  { subst.
    apply sub_reflexivity; applys typing_regular Typ.
  }
  clear HeqT.
  generalize dependent Sub.
  generalize dependent R.
  generalize dependent C.
  dependent induction Typ; intros D Q Sub.
  - exists C, R.
    assert (WfCR : wf_typ Γ S (C # R)).
    { destruct (wf_typ_ctx_bind_typ x (C # R) Γ ltac:(assumption) ltac:(assumption)) as [D' [Q' [Eq Wf]]]...
      inversion Eq...
    }
    assert (WfDQ : wf_typ Γ S (D # Q)).
    { applys sub_regular Sub. }
    inversion WfCR; inversion WfDQ; subst...
    inversion Sub...
  - assert (WfR : wf_typ Γ S R).
    { apply sub_regular in H... }
    assert (RsubDQ : sub Γ S R (D # Q)).
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

Lemma wf_typ_free_in_ctx : forall x Γ S T,
  wf_typ Γ S T ->
  x ∉ dom Γ ->
  x ∉ fv_tt T.
Proof with eauto.
  intros * WfTyp Dom.
  dependent induction WfTyp; simpl in *...
  - apply binds_In in H.
    fsetdec.
  - pick fresh y for (L `union`A dom Γ `union`A {{ x }}A).
    specialize (H0 y ltac:(fsetdec) ltac:(fsetdec)).
    apply notin_fv_tt_open_ct in H0.
    specialize (IHWfTyp Dom).
    fsetdec.
  - pick fresh y for (L `union`A dom Γ `union`A {{ x }}A).
    specialize (H1 y ltac:(fsetdec) ltac:(fsetdec)).
    apply notin_fv_tt_open_tt in H1.
    specialize (IHWfTyp Dom).
    fsetdec.
Qed.

Lemma pure_wf_typ_no_fv_tt : forall x S T,
  wf_typ nil S T ->
  x ∉ fv_tt T.
Proof with eauto.
  intros * Wf.
  apply wf_typ_free_in_ctx with (Γ := nil) (S := S)...
Qed.

Lemma typing_through_subst_te : forall Q Γ Δ Z e T P S,
  typing (Δ ++ [(Z, bind_sub Q)] ++ Γ) S e T ->
  sub Γ S P Q ->
  typing (map (subst_tb Z P) Δ ++ Γ) S (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 4 using wf_ctx_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt,
                         wf_typ_from_binds_typ,
                         wf_typ_ignores_sub_bindings,
                         wf_typ_ignores_typ_bindings.
  intros * Typ PsubQ.
  assert (WfCtx : wf_ctx (Δ ++ [(Z, bind_sub Q)] ++ Γ) S) by applys typing_regular Typ.
  assert (PureP : pure_type P).
  { applys sub_pure_type PsubQ.
    apply wf_ctx_tail in WfCtx.
    inversion WfCtx...
  }
  assert (ZNotInDomΓ : Z ∉ dom Γ).
  { eapply fresh_mid_tail, uniq_from_wf_ctx.
    applys typing_regular Typ.
  }
  remember (Δ ++ [(Z, bind_sub Q)] ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ; subst;
    simpl subst_te in *; simpl subst_tt in *.
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    analyze_binds_uniq Binds...
    + SCase "x ∈ dom Δ".
      apply typing_var with (C := C)...
      replace (bind_typ (C # subst_tt Z P R))
         with (subst_tb Z P (bind_typ (C # R)))
           by reflexivity.
      apply binds_app_2, binds_map...
    + SCase "x ∈ dom Γ".
      rewrite <- subst_tt_fresh.
      * apply typing_var with (C := C)...
      * apply notin_fv_wf_typ with (Γ := Γ) (S := S)...
        apply wf_typ_from_binds_typ with (S := S) in BindsTac0...
        inversion BindsTac0...
  - Case "typing_loc".
    apply typing_loc with (C := C)...
    rewrite <- subst_tt_fresh...
    assert (WfTyp : wf_typ nil S (C # R)). {
      apply wf_typ_from_wf_store_ctx_nil with (S := S) in H0.
      2: applys sub_regular PsubQ.
      inversion H0; subst...
    }
    assert (WfR : wf_typ nil S R) by (inversion WfTyp; eauto).
    assert (PureR : pure_type R) by (inversion WfTyp; eauto).
    assert (Z ∉ fv_ct R) by (eapply wf_typ_notin_fv_ct; eauto).
    assert (Z ∉ fv_tt R) by (eapply pure_wf_typ_no_fv_tt; eauto).
    fsetdec.
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
      assumption.
      apply wf_ctx_typ...
      reflexivity.
  - Case "typing_app".
    destruct x...
    + destruct v... 2: inversion H0... 
      assert (Z <> a).
      { destruct (typing_var_implies_binds_typ _ _ _ _ _ Typ2) as [C' [R' [Binds _]]].
        analyze_binds_uniq Binds...
      }
      simpl.
      replace (subst_tt Z P (open_ct T (cse_fvar a)))
         with (open_ct (subst_tt Z P T) (cse_fvar a))
           by (apply open_ct_subst_tt; eauto* )...
    + simpl.
      replace (subst_tt Z P (open_ct T (cse_loc l)))
         with (open_ct (subst_tt Z P T) (cse_loc l))
           by (apply open_ct_subst_tt; eauto* )...
    - Case "typing_let".
      pick fresh y and apply typing_let...
      rewrite <- subst_te_open_ve...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ (C1 # R1))] ++ Δ) ++ Γ).
      apply H0.
      clear - Fr; fsetdec.
      assumption.
      2: reflexivity.
      assert (WfC1R1 : wf_typ (Δ ++ [(Z, bind_sub Q)] ++ Γ) S (C1 # R1)) by applys typing_regular Typ.
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
      assumption.
      2: reflexivity.
      apply wf_ctx_sub...
  - Case "typing_tapp".
    rewrite subst_tt_open_tt...
  - Case "typing_box".
    apply typing_box...
    assert (WfCR : wf_typ (Δ ++ [(Z, bind_sub Q)] ++ Γ) S (C # R)).
    { applys typing_regular Typ. }
    assert (WfC : wf_cse (Δ ++ [(Z, bind_sub Q)] ++ Γ) S C).
    { inversion WfCR... }
    apply (wf_cse_subst_tb _ _ Q Z P C)...
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cse_subst_tb...
  - Case "typing_sub".
    eapply typing_sub...
    apply sub_reflexivity...
Qed.

(*
Lemma typing_through_open_ve_typing : forall Γ S (x y : atom) U e T,
  y ∉ (fv_ct T `union`A fv_ve e `union`A fv_ce e) ->
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
  y ∉ (fv_ct T `union`A fv_ve e `union`A fv_ce e) ->
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

Lemma typing_through_open_te : forall Γ S (Y : atom) e T P Q,
  Y ∉ (fv_tt T `union`A fv_ct T `union`A fv_te e `union`A fv_ce e) ->
  typing ([(Y, bind_sub Q)] ++ Γ) S (open_te e Y) (open_tt T Y) ->
  sub Γ S P Q ->
  typing Γ S (open_te e P) (open_tt T P).
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

 Lemma subst_vv_saves_fvar_like : forall z u v,
   fvar_like v ->
   fvar_like u ->
   fvar_like (subst_vv z u v).
Proof with eauto.
  intros * FvarV FvarU.
  destruct FvarV; simpl...
  destruct (x == z); subst...
Qed.

Hint Resolve subst_vv_saves_fvar_like : core.

(* Location lemmas *)
Lemma typing_loc_implies_binds : forall Γ S (l: loc) C R,
  typing Γ S l (C # R) ->
  exists D Q, StoreImpl.binds l (D # Q) S
           /\ subcapt Γ S (cse_loc l) C
           /\ wf_cse Γ S D
           /\ sub Γ S Q R
           /\ pure_type R.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
  - exists C0, R.
    repeat split...
    all: apply wf_typ_from_wf_store_ctx with (Γ := Γ) in H0...
    all: inversion H0; subst...
    apply sub_reflexivity...
  - assert (Typ': typing Γ S l (C # R)) by eauto using sub_transitivity.
    apply typing_cse_all_bound_locs with (L := l) in Typ.
    destruct Typ as [T Binds].
    assert (wf_store_ctx S) by applys sub_regular H.
    destruct (sub_capt_type _ R0 (C # R) _ H) as [_ Ex].
    destruct (Ex ltac:(eauto)) as [D' [Q' Eq]]; subst.
    destruct (IHTyp l D' Q' eq_refl eq_refl) as [D0 [Q0 [Binds' [LsubD' [WfD0 [Q0subQ' PureQ']]]]]].
    exists D0, Q0.
    repeat split...
    + apply subcapt_transitivity with (Q := D')...
      inversion H; subst...
    + apply sub_transitivity with (Q := Q')...
      inversion H; subst...
    + assert (wf_typ Γ S (C # R)) by applys typing_regular Typ'.
      inversion H1; subst...
    + simpl. flsetdec.
Qed.

Lemma subst_ct_open_ct_loc : forall x l T,
  subst_ct x (cse_loc l) (open_ct T (cse_fvar x)) = open_ct (subst_ct x (cse_loc l) T) (cse_loc l).
Proof with eauto.
  intros.
  unfold open_ct.
  rewrite subst_ct_open_rec...
  simpl. destruct (x == x); try fsetdec...
Qed.

Lemma help : forall x l C T,
  cset C ->
  (subst_ct x C (open_ct T (cse_loc l))) = open_ct (subst_ct x C T) (cse_loc l).
Proof with eauto.
  intros.
  unfold open_ct.
  rewrite subst_ct_open_rec...
Qed.

Lemma typing_loc_through_subst_ve : forall Γ Δ x T C R e (l : loc) S,
  typing (Δ ++ [(x, bind_typ (C # R))] ++ Γ) S e T ->
  typing Γ S l (C # R) ->
  typing (map (subst_cb x (cse_loc l)) Δ ++ Γ) S (subst_ve x l (cse_loc l) e) (subst_ct x (cse_loc l) T).
Proof with eauto using sub_reflexivity.
  intros * Typ lTyp.
  forwards (WfStore & WfCtx & _ & WfT): typing_regular Typ.
  assert (WfCtx' : wf_ctx Γ S) by (repeat apply wf_ctx_tail in WfCtx; assumption).
  destruct (typing_loc_implies_binds _ _ _ _ _ lTyp) as [D [Q [Binds [usubC [WfD [QsubR PureR]]]]]].
  assert (PureQ : pure_type Q) by (applys sub_pure_type QsubR; eauto).
  assert (WfL : wf_cse Γ S (cse_loc l))
    by (eapply wf_cse_loc_from_binds; eauto).
  assert (WfCtxSubst : wf_ctx (map (subst_cb x (cse_loc l)) Δ ++ Γ) S) by (eapply wf_ctx_subst_cb; eauto).
  assert (xNotInΓ : x ∉ dom Γ) by (apply fresh_mid_tail with (F := Δ) (a := (bind_typ (C # R))); eauto).
  assert (xNotInΔ : x ∉ dom Δ) by (eapply fresh_mid_head; eauto).
  assert (xNotInQ : x ∉ fv_ct Q) by (eapply wf_typ_notin_fv_ct; eauto).
  assert (xNotInR : x ∉ fv_ct R) by (eapply wf_typ_notin_fv_ct; eauto).
  dependent induction Typ; simpl.
  - Case "typing_var".
    destruct (x0 == x); subst; try (exfalso; fsetdec).
    + SCase "x0 = x".
      rename select (binds x _ _) into Binds'.
      analyze_binds_uniq Binds'...
      destruct (x == x); try fsetdec.
      inversion select (bind_typ _ = bind_typ _); subst.
      rewrite_nil_concat.
      eapply typing_weakening.
      2: assumption.
      apply typing_sub with (R := cse_loc l # R); simpl in *...
      apply sub_capt...
      -- rewrite <- subst_ct_fresh...
      -- rewrite <- subst_ct_fresh...
    + SCase "x0 <> x".
      rename select (binds x0 _ _) into Binds'.
      analyze_binds_uniq Binds'; destruct (x == x0); subst; simpl; destruct (x0 == x0); try fsetdec.
      * apply uniq_from_wf_ctx in H...
      * destruct (x0 == x); destruct (x == x0); try fsetdec; simpl.
        eapply typing_var with (C := subst_cse x (cse_loc l) C0)...
        rename select (binds x0 _ _) into Binds'.
        replace (bind_typ (subst_cse x (cse_loc l) C0 # subst_ct x (cse_loc l) R0))
           with (subst_cb x (cse_loc l) (bind_typ (C0 # R0)))
             by reflexivity.
        apply binds_app_2, binds_map, Binds'.
      * destruct (x0 == x); destruct (x == x0); try fsetdec; simpl.
        eapply typing_var with (C := C0)...
        apply binds_app_3...
        rewrite <- subst_ct_fresh...
        eapply wf_typ_notin_fv_ct with (Γ := Γ)...
        rename select (binds x0 _ _) into Binds'.
        destruct (wf_typ_ctx_bind_typ _ _ _ _ WfCtx' Binds') as [D0 [Q0 [Eq WfD0Q0]]]; inversion Eq; subst; clear Eq.
        inversion WfD0Q0; subst...
  - Case "typing_loc".
    apply typing_loc with (C := C0)...
    rewrite <- subst_ct_fresh. assumption.
    apply wf_typ_from_wf_store_ctx_nil in H0.
    inversion H0; subst.
    apply wf_typ_notin_fv_ct with (x := x) in H6.
    assumption. fsetdec. assumption.
  - Case "typing_abs".
    rewrite subst_cse_loc_cv_commutes_with_subst_ve.
    pick fresh y and apply typing_abs.
    + replace (subst_cse x (cse_loc l) C0 # subst_ct x (cse_loc l) R0)
         with (subst_ct x (cse_loc l) (C0 # R0))
           by reflexivity.
      eapply wf_typ_subst_cb...
    + rename select (forall x0 : atom, x0 ∉ L -> typing _ S (open_ve _ _ _) (open_ct _ _)) into e1Typ.
      specialize (e1Typ y ltac:(clear - Fr; fsetdec)).
      assert (Neq : x <> y) by (clear - Fr; fsetdec).
      rewrite_env (map (subst_cb x (cse_loc l)) ([(y, bind_typ (C0 # R0))] ++ Δ) ++ Γ).
      rewrite subst_ct_open_ct_var.
      2-3: auto.
      rewrite subst_ve_open_ve_var.
      2-3: auto.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH with (C := C) (R := R)...
      eapply wf_ctx_subst_cb...
      constructor...
  - Case "typing_app".
    destruct x0.
    + destruct v. 2: exfalso; inversion H0.
      destruct (a == x) eqn:Hx0_a; subst; simpl.
      * destruct (x == x); try fsetdec...
        unshelve epose proof (IHTyp1 Γ Δ x C R _ _ _ _ _ _ D0 Q0 _ _ _ _ _ _ _ _ _ _ _ _) as IH1...
        unshelve epose proof (IHTyp2 Γ Δ x C R _ _ _ _ _ _ D0 Q0 _ _ _ _ _ _ _ _ _ _ _ _) as IH2...
        destruct f. destruct v. 2: exfalso; inversion H.
        simpl in *.
        destruct (a == x) eqn:Hf_a; rewrite subst_ct_open_ct_loc...
        -- destruct (a == x); destruct (x == x); subst; try fsetdec.
           eapply typing_app with (D := subst_cse x (cse_loc l) D) (Q := subst_ct x (cse_loc l) Q) (C := subst_cse x (cse_loc l) C0); try auto.
        -- destruct (x == x); try fsetdec.
           eapply typing_app with (D := subst_cse x (cse_loc l) D) (Q := subst_ct x (cse_loc l) Q) (C := subst_cse x (cse_loc l) C0); try auto.
        -- rewrite subst_ct_open_ct_loc.
           eapply typing_app with (D := subst_cse x (cse_loc l) D) (Q := subst_ct x (cse_loc l) Q) (C := subst_cse x (cse_loc l) C0); try auto.
           replace (subst_cse x (cse_loc l) D # subst_ct x (cse_loc l) Q) with (subst_ct x (cse_loc l) (D # Q)) by reflexivity.
           simpl in IH2; destruct (x == x); try fsetdec...
      * rewrite <- subst_ct_open_ct_var...
        destruct (a == x); subst; try fsetdec.
        apply typing_app with (D := subst_cse x (cse_loc l) D) (Q := subst_ct x (cse_loc l) Q) (C := subst_cse x (cse_loc l) C0) (T := subst_ct x (cse_loc l) T). auto. auto.
        -- replace (subst_cse x (cse_loc l) D # subst_ct x (cse_loc l) Q) with (subst_ct x (cse_loc l) (D # Q)) by reflexivity.
           replace (exp_var_like (subst_vv x l f)) with (subst_ve x l (cse_loc l) f) by (destruct f; auto).
           eapply IHTyp1...
        -- replace (subst_cse x (cse_loc l) D # subst_ct x (cse_loc l) Q) with (subst_ct x (cse_loc l) (D # Q)) by reflexivity.
           replace (exp_var_like (var_like_var a)) with (subst_ve x l (cse_loc l) a).
           eapply IHTyp2...
           simpl. destruct (a == x)...
           fsetdec.
    + simpl in *.
      erewrite help...
      apply typing_app with (D := subst_cse x (cse_loc l) D) (Q := subst_ct x (cse_loc l) Q) (C := subst_cse x (cse_loc l) C0) (T := subst_ct x (cse_loc l) T). auto. auto.
      * replace (subst_cse x (cse_loc l) D # subst_ct x (cse_loc l) Q) with (subst_ct x (cse_loc l) (D # Q)) by reflexivity.
        replace (exp_var_like (subst_vv x l f)) with (subst_ve x l (cse_loc l) f) by (destruct f; auto).
        eapply IHTyp1...
      * replace (subst_cse x (cse_loc l) D # subst_ct x (cse_loc l) Q) with (subst_ct x (cse_loc l) (D # Q)) by reflexivity.
        replace (exp_var_like l0) with (subst_ve x l (cse_loc l) l0) by (simpl; reflexivity).
        eapply IHTyp2...
  - Case "typing_let".
    pick fresh y and apply typing_let.
    + eapply IHTyp...
    + rewrite subst_ve_open_ve_var...
      fold subst_ct.
      replace ([(y, bind_typ (subst_cse x (cse_loc l) C1 # subst_ct x (cse_loc l) R1))] ++ map (subst_cb x (cse_loc l)) Δ ++ Γ)
         with (map (subst_cb x (cse_loc l)) ([(y, bind_typ (C1 # R1))] ++ Δ) ++ Γ)
           by reflexivity.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH...
      * apply wf_ctx_typ...
      * rewrite app_assoc.
        apply wf_typ_weaken_head...
      * eapply wf_ctx_subst_cb...
        eapply wf_ctx_typ...
  - Case "typing_tabs".
    rewrite subst_cse_loc_cv_commutes_with_subst_ve.
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_subst_cb...
    + apply subst_ct_pure_type...
    + rename select (forall X : atom, X ∉ L -> typing _ _ (open_te _ _) (open_tt _ _)) into e1Typ.
      specialize (e1Typ Y ltac:(clear - Fr; fsetdec)).
      assert (Neq : x <> Y) by (clear - Fr; fsetdec).
      rewrite_env (map (subst_cb x (cse_loc l)) ([(Y, bind_sub V)] ++ Δ) ++ Γ).
      rewrite subst_ve_open_te_var.
      2-3: auto.
      rewrite subst_ct_open_tt_var.
      2-3: auto.
      rename select (forall X : atom, X ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH...
      eapply wf_ctx_subst_cb...
  - Case "typing_tapp".
    destruct x0.
    + destruct v. 2: exfalso; inversion H.
      destruct (a == x); subst; simpl.
      * destruct (x == x); try fsetdec.
        unshelve epose proof (IHTyp Γ Δ x C R _ _ _ _ _ _ D Q0 _ _ _ _ _ _ _ _ _ _ _ _) as IH...
        rewrite subst_ct_open_tt; try auto.
        eapply typing_tapp with (C := subst_cse x (cse_loc l) C0) (Q := subst_ct x (cse_loc l) Q); try auto.
        simpl in IH; destruct (x == x); try fsetdec...
        eapply sub_through_subst_ct...
      * rewrite subst_ct_open_tt...
        destruct (a == x); subst; try fsetdec.
        eapply typing_tapp with (C := subst_cse x (cse_loc l) C0) (Q := subst_ct x (cse_loc l) Q). auto. auto.
        -- replace (subst_cse x (cse_loc l) C0 # ∀ [subst_ct x (cse_loc l) P] subst_ct x (cse_loc l) T) with (subst_ct x (cse_loc l) (C0 # ∀ [P] T)) by reflexivity.
           replace (exp_var_like a) with (subst_ve x l (cse_loc l) a).
           eapply IHTyp...
           simpl. destruct (a == x)...
           fsetdec.
        -- apply sub_through_subst_ct with (CU := C) (U := R)...
    + simpl in *.
      erewrite subst_ct_open_tt.
      eapply typing_tapp with (C := subst_cse x (cse_loc l) C0); try auto.
      eapply IHTyp...
      apply sub_through_subst_ct with (CU := C) (U := R)...
      constructor.
  - Case "typing_box".
    destruct x0.
    + destruct v. 2: exfalso; inversion H.
      simpl. destruct (a == x); subst; simpl.
      * destruct (x == x); try fsetdec.
        unshelve epose proof (IHTyp Γ Δ x C R _ _ _ _ _ _ D Q _ _ _ _ _ _ _ _ _ _ _ _) as IH...
        eapply typing_box; try auto.
        simpl in IH; destruct (x == x); try fsetdec...
        apply wf_cse_subst_cb with (Q := C # R)...
      * apply typing_box; try auto.
        replace (exp_var_like a) with (subst_ve x l (cse_loc l) a).
        eapply IHTyp...
        simpl. destruct (a == x); try fsetdec...
        eapply wf_cse_subst_cb...
    + apply typing_box; try auto.
      eapply IHTyp...
      apply wf_cse_subst_cb with (Q := C # R)...
  - Case "typing_unbox".
    destruct x0.
    + destruct v. 2: exfalso; inversion H.
      simpl. destruct (a == x); subst; simpl.
      * destruct (x == x); try fsetdec.
        unshelve epose proof (IHTyp Γ Δ x C R _ _ _ _ _ _ D Q _ _ _ _ _ _ _ _ _ _ _ _) as IH...
        apply typing_unbox; try auto.
        simpl in IH; destruct (x == x); try fsetdec...
        apply wf_cse_subst_cb with (Q := C # R)...
      * apply typing_unbox; try auto.
        replace (exp_var_like a) with (subst_ve x l (cse_loc l) a).
        eapply IHTyp...
        simpl. destruct (a == x); try fsetdec...
        apply wf_cse_subst_cb with (Q := C # R)...
    + apply typing_unbox; try auto.
      eapply IHTyp...
      apply wf_cse_subst_cb with (Q := C # R)...
  - Case "typing_sub".
    Set Printing Coercions.
    apply typing_sub with (R := subst_ct x (cse_loc l) R0).
    + eapply IHTyp...
    + apply sub_through_subst_ct with (CU := C) (U := R)...
Qed.

Lemma typing_through_open_ve_typing_loc : forall Γ S (l: loc) (y : atom) U e T,
  y ∉ (fv_ct T `union`A fv_ve e `union`A fv_ce e) ->
  typing ([(y, bind_typ U)] ++ Γ) S (open_ve e y (cse_fvar y)) T ->
  typing Γ S l U ->
  typing Γ S (open_ve e l (cse_loc l)) T.
Proof with eauto*.
  intros * NotIn Typ lTyp.
  assert (WfCtx : wf_ctx ([(y, bind_typ U)] ++ Γ) S) by applys typing_regular Typ.
  inversion WfCtx; subst.
  destruct (typing_loc_implies_binds _ _ _ _ _ lTyp) as [D [Q [Binds [xsubC [WfD [QsubR PureR]]]]]].
  rewrite_env (map (subst_cb y (cse_loc l)) ∅ ++ Γ).
  replace (open_ve e l (cse_loc l))
     with (subst_ve y l (cse_loc l) (open_ve e y (cse_fvar y)))
       by (rewrite <- subst_ve_intro; auto).
  replace T
     with (subst_ct y (cse_loc l) T)
       by (rewrite <- subst_ct_fresh; auto).
  eapply typing_loc_through_subst_ve with (C := cse_loc l) (R := Q).
  - eapply typing_narrowing_typ with (D := C) (Q := R)...
    apply sub_capt...
    applys sub_pure_type QsubR...
  - eapply typing_loc...
Qed.

Lemma typing_through_open_ve_typing_open_loc : forall Γ S (y : atom) (l : loc) U e T,
  y ∉ (fv_ct T `union`A fv_ve e `union`A fv_ce e) ->
  typing ([(y, bind_typ U)] ++ Γ) S (open_ve e y (cse_fvar y)) (open_ct T (cse_fvar y)) ->
  typing Γ S l U ->
  typing Γ S (open_ve e l (cse_loc l)) (open_ct T (cse_loc l)).
Proof with eauto*.
  intros * NotIn Typ lTyp.
  assert (WfCtx : wf_ctx ([(y, bind_typ U)] ++ Γ) S) by applys typing_regular Typ.
  inversion WfCtx; subst.
  destruct (typing_loc_implies_binds _ _ _ _ _ lTyp) as [D [Q [Binds [lsubC [WfD [QsubR PureR]]]]]].
  rewrite_env (map (subst_cb y (cse_loc l)) ∅ ++ Γ).
  replace (open_ve e l (cse_loc l))
     with (subst_ve y l (cse_loc l) (open_ve e y (cse_fvar y)))
       by (rewrite <- subst_ve_intro; auto).
  replace (open_ct T (cse_loc l))
     with (subst_ct y (cse_loc l) (open_ct T (cse_fvar y)))
       by (rewrite <- subst_ct_intro; auto).
  eapply typing_loc_through_subst_ve with (C := cse_loc l) (R := Q).
  - eapply typing_narrowing_typ with (D := C) (Q := R)...
    apply sub_capt...
    applys sub_pure_type QsubR...
  - eapply typing_loc...
Qed.
