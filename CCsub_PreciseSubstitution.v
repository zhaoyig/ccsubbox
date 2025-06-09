Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Precise.
Require Import CCsub_Substitution.

Set Nested Proofs Allowed.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma prec_typing_through_subst_ve : forall Γ Δ x T C R e (u : atom) S,
  prec_typing (Δ ++ [(x, bind_typ (C # R))] ++ Γ) S e T ->
  prec_typing Γ S u (C # R) ->
  prec_typing (map (subst_cb x (cse_fvar u)) Δ ++ Γ) S (subst_ve x u (cse_fvar u) e) (subst_ct x (cse_fvar u) T).
Proof with eauto*.
  intros * Typ uTyp.
  forwards (WfStore & WfCtx & _ & WfT): prec_typing_regular Typ.
  assert (WfCtx' : wf_ctx Γ S) by (repeat apply wf_ctx_tail in WfCtx; assumption).
  inversion uTyp; subst.
  assert (WfU : wf_cse Γ S (cse_fvar u))
    by (eapply wf_cse_from_binds; eauto).
  assert (WfCtxSubst : wf_ctx (map (subst_cb x (cse_fvar u)) Δ ++ Γ) S) by (eapply wf_ctx_subst_cb; eauto).
  assert (uNotInΔ : u ∉ dom Δ).
  { eapply tail_not_in_head...
    apply binds_In in H5.
    simpl; fsetdec.
  }
  assert (xNotInΓ : x ∉ dom Γ) by (apply fresh_mid_tail with (F := Δ) (a := (bind_typ (C0 # R))); eauto).
  assert (xNotInΔ : x ∉ dom Δ) by (eapply fresh_mid_head; eauto).
  assert (xNotInR : x ∉ fv_ct R). {
    eapply wf_typ_notin_fv_ct with (Γ := Γ); eauto.
    destruct (prec_typing_regular _ _ _ _ uTyp) as [_ [_ [_ WfUR]]].
    inversion WfUR...
  }
  dependent induction Typ; simpl.
  - Case "typing_var".
    destruct (x0 == x); subst; try (exfalso; fsetdec).
    + SCase "x0 = x".
      rename select (binds x _ _) into Binds'.
      binds_cases Binds'.
      * exfalso; simpl in *; fsetdec.
      * inversion select (bind_typ _ = bind_typ _); subst.
        rewrite_nil_concat.
        eapply prec_typing_weakening.
        2: assumption.
        destruct (x == x); try fsetdec.
        simpl.
        enough (R = subst_ct x (cse_fvar u) R)...
        rewrite <- subst_ct_fresh...
      * rename select (binds x _ _) into Binds'.
        apply binds_In in Binds'.
        contradiction.
    + SCase "x0 <> x".
      rename select (binds x0 _ _) into Binds'.
      binds_cases Binds'; destruct (x == x0); subst; simpl; destruct (x0 == x0); try fsetdec.
      * destruct (x0 == x); destruct (x == x0); try fsetdec; simpl.
        eapply prec_typing_var with (C := C)...
        apply binds_tail...
        rewrite <- subst_ct_fresh.
        assumption.
        eapply wf_typ_notin_fv_ct with (Γ := Γ)...
        rename select (binds x0 _ _) into Binds'.
        destruct (wf_typ_ctx_bind_typ _ _ _ _ WfCtx' Binds') as [D0 [Q0 [Eq WfD0Q0]]]; inversion Eq; subst; clear Eq.
        inversion WfD0Q0; subst...
      * destruct (x0 == x); destruct (x == x0); try fsetdec; simpl.
        eapply prec_typing_var with (C := subst_cse x (cse_fvar u) C)...
        rename select (binds x0 _ _) into Binds'.
        replace (bind_typ (subst_cse x (cse_fvar u) C # subst_ct x (cse_fvar u) R0))
           with (subst_cb x (cse_fvar u) (bind_typ (C # R0)))
             by reflexivity.
        apply binds_head, binds_map, Binds'.
  - Case "typing_abs".
    rewrite subst_cse_cv_commutes_with_subst_ve.
    pick fresh y and apply prec_typing_abs.
    + replace (subst_cse x (cse_fvar u) C # subst_ct x (cse_fvar u) R0)
         with (subst_ct x (cse_fvar u) (C # R0))
           by reflexivity.
      eapply wf_typ_subst_cb...
    + rename select (forall x0 : atom, x0 ∉ L -> prec_typing _ S (open_ve _ _ _) (open_ct _ _)) into e1Typ.
      specialize (e1Typ y ltac:(clear - Fr; fsetdec)).
      assert (Neq : x <> y) by (clear - Fr; fsetdec).
      rewrite_env (map (subst_cb x (cse_fvar u)) ([(y, bind_typ (C # R0))] ++ Δ) ++ Γ).
      rewrite subst_ct_open_ct_var.
      2-3: auto.
      rewrite subst_ve_open_ve_var.
      2-3: auto.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH with (C0 := C0) (R1 := R)...
      eapply wf_ctx_subst_cb...
  - Case "typing_app".
    assert (Iff : (if f == x then (var_f u) else (var_f f)) = var_f (if f == x then u else f))
      by (destruct_if; reflexivity).
    rewrite Iff.
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      unfold open_ct.
      rewrite subst_ct_open_rec...
      simpl. simpl. destruct (x == x); try fsetdec...
      eapply prec_typing_app.
      * rewrite <- Iff.
        eapply IHTyp1...
      * fold subst_ct.
        replace (subst_cse x (cse_fvar u) D # subst_ct x (cse_fvar u) Q)
           with (subst_ct x (cse_fvar u) (D # Q))
             by reflexivity.
        replace (exp_var (var_f u))
           with (subst_ve x u (cse_fvar u) (exp_var (var_f x))).
        eapply IHTyp2...
        simpl; destruct (x == x); try fsetdec.
    + SCase "x0 <> x".
      rewrite <- subst_ct_open_ct_var...
      apply prec_typing_app with (D := subst_cse x (cse_fvar u) D) (Q := subst_ct x (cse_fvar u) Q) (C := subst_cse x (cse_fvar u) C) (T := subst_ct x (cse_fvar u) T).
      * replace (subst_cse x (cse_fvar u) C # ∀ ((subst_cse x (cse_fvar u) D # subst_ct x (cse_fvar u) Q)) subst_ct x (cse_fvar u) T)
           with (subst_ct x (cse_fvar u) (C # ∀ (D # Q) T))
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
    pick fresh y and apply prec_typing_let.
    + eapply IHTyp...
    + rewrite subst_ve_open_ve_var...
      fold subst_ct.
      replace ([(y, bind_typ (subst_cse x (cse_fvar u) C1 # subst_ct x (cse_fvar u) R1))] ++ map (subst_cb x (cse_fvar u)) Δ ++ Γ)
         with (map (subst_cb x (cse_fvar u)) ([(y, bind_typ (C1 # R1))] ++ Δ) ++ Γ)
           by reflexivity.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : ctx), _) into IH.
      eapply IH...
      * rewrite concat_assoc.
        apply wf_typ_weaken_head.
        assumption. constructor...
      * apply wf_ctx_typ...
      * eapply wf_ctx_subst_cb...
        eapply wf_ctx_typ...
  - Case "typing_tabs".
    rewrite subst_cse_cv_commutes_with_subst_ve.
    pick fresh Y and apply prec_typing_tabs.
    + eapply wf_typ_subst_cb...
    + apply subst_ct_pure_type...
    + rename select (forall X : atom, X ∉ L -> prec_typing _ _ (open_te _ _) (open_tt _ _)) into e1Typ.
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
    assert (Ifx0 : (if x0 == x then (var_f u) else (var_f x0)) = var_f (if x0 == x then u else x0))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    rewrite subst_ct_open_tt...
    eapply prec_typing_tapp with (Q := subst_ct x (cse_fvar u) Q) (C := subst_cse x (cse_fvar u) C) (x := (if x0 == x then u else x0)).
    + replace (subst_cse x (cse_fvar u) C # ∀ [subst_ct x (cse_fvar u) Q] subst_ct x (cse_fvar u) T)
         with (subst_ct x (cse_fvar u) (C # ∀ [Q] T))
           by reflexivity.
      rewrite <- Ifx0.
      eapply IHTyp...
    + apply sub_through_subst_ct with (CU := cse_fvar u) (U := R)...
  - Case "typing_box".
    assert (Ifx0 : (if x0 == x then (var_f u) else (var_f x0)) = var_f (if x0 == x then u else x0))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    eapply prec_typing_box.
    + replace (subst_cse x (cse_fvar u) C0 # subst_ct x (cse_fvar u) R0)
         with (subst_ct x (cse_fvar u) (C0 # R0))
           by reflexivity.
      rewrite <- Ifx0.
      eapply IHTyp...
    + apply (wf_cse_over_subst Γ Δ (C # R) x (cse_fvar u) C)...
      eapply wf_cse_ignores_typ_bindings; eauto.
  - Case "typing_unbox".
    assert (Ifx0 : (if x0 == x then (var_f u) else (var_f x0)) = var_f (if x0 == x then u else x0))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    apply prec_typing_unbox.
    + replace ({} # (□ subst_cse x (cse_fvar u) C # subst_ct x (cse_fvar u) R0))
         with (subst_ct x (cse_fvar u) ({} # (□ C # R0))).
      2: {
        simpl.
        f_equal...
      }
      rewrite <- Ifx0.
      eapply IHTyp...
    + eapply wf_cse_over_subst...
Qed.

(* Lemma wf_typ_fv_tt_in_ctx : forall x Γ S T, *)
(*   wf_typ Γ S T -> *)
(*   x ∉ dom Γ -> *)
(*   x ∉ fv_tt T. *)
(* Proof with eauto 3. *)
(*   intros * WfTyp Dom. *)
(*   dependent induction WfTyp; simpl in *... *)
(*   - apply binds_In in H. *)
(*     fsetdec. *)
(*   - pick fresh y for (L `u`A dom Γ `u`A {x}A). *)
(*     specialize (H0 y ltac:(fsetdec) ltac:(fsetdec)). *)
(*     apply notin_fv_tt_open_ct in H0. *)
(*     specialize (IHWfTyp Dom). *)
(*     fsetdec. *)
(*   - pick fresh y for (L `u`A dom Γ `u`A {x}A). *)
(*     specialize (H1 y ltac:(fsetdec) ltac:(fsetdec)). *)
(*     apply notin_fv_tt_open_tt in H1. *)
(*     specialize (IHWfTyp Dom). *)
(*     fsetdec. *)
(* Qed. *)
(**)
(* Lemma pure_wf_typ_no_fv_tt : forall x S T, *)
(*   wf_typ nil S T -> *)
(*   x ∉ fv_tt T. *)
(* Proof with eauto. *)
(*   intros * Wf. *)
(*   apply wf_typ_fv_tt_in_ctx with (Γ := nil) (S := S)... *)
(* Qed. *)
(**)
Lemma prec_typing_through_subst_te : forall Q Γ Δ Z e T P S,
  prec_typing (Δ ++ [(Z, bind_sub Q)] ++ Γ) S e T ->
  sub Γ S P Q ->
  prec_typing (map (subst_tb Z P) Δ ++ Γ) S (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 4 using wf_ctx_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt,
                         wf_typ_from_binds_typ,
                         wf_typ_ignores_sub_bindings,
                         wf_typ_ignores_typ_bindings.
  intros * PTyp PsubQ.
  assert (WfCtx : wf_ctx (Δ ++ [(Z, bind_sub Q)] ++ Γ) S) by applys prec_typing_regular PTyp.
  assert (PureP : pure_type P).
  { applys sub_pure_type PsubQ.
    apply wf_ctx_tail in WfCtx.
    inversion WfCtx...
  }
  assert (ZNotInDomΓ : Z ∉ dom Γ).
  { eapply fresh_mid_tail, ok_from_wf_ctx.
    applys prec_typing_regular PTyp.
  }
  remember (Δ ++ [(Z, bind_sub Q)] ++ Γ).
  generalize dependent Δ.
  induction PTyp; intros Δ EQ; subst;
    simpl subst_te in *; simpl subst_tt in *.
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds.
    + SCase "x ∈ dom Γ".
      rewrite <- subst_tt_fresh.
      * apply prec_typing_var with (C := C)...
      * apply notin_fv_wf_typ with (Γ := Γ) (S := S)...
        apply wf_typ_from_binds_typ with (S := S) in H1.
        inversion H1; subst...
        applys sub_regular PsubQ.
    + SCase "x ∈ dom Δ".
      apply prec_typing_var with (C := C)...
      replace (bind_typ (C # subst_tt Z P R))
         with (subst_tb Z P (bind_typ (C # R)))
           by reflexivity.
      apply binds_head, binds_map.
      assumption.
  - Case "typing_abs".
    replace (exp_cv e1)
       with (exp_cv (subst_te Z P e1))
         by (symmetry; apply subst_te_fresh_exp_cv).
    pick fresh x and apply prec_typing_abs.
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
    assert (Z <> x).
    { inversion PTyp2; subst.
      rename select (binds _ _ _) into Binds.
      binds_cases Binds; simpl_env in *...
      assert (Z ∉ dom Δ) by (eapply fresh_mid_head; eauto* ).
      apply binds_In in H0.
      fsetdec.
    }
    simpl.
    replace (subst_tt Z P (open_ct T (cse_fvar x)))
       with (open_ct (subst_tt Z P T) (cse_fvar x))
         by (apply open_ct_subst_tt; eauto* )...
    eapply prec_typing_app...
    - Case "typing_let".
      pick fresh y and apply prec_typing_let...
      rewrite <- subst_te_open_ve...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ (C1 # R1))] ++ Δ) ++ Γ).
      apply H0.
      clear - Fr; fsetdec.
      assumption.
      2: reflexivity.
      assert (WfC1R1 : wf_typ (Δ ++ [(Z, bind_sub Q)] ++ Γ) S (C1 # R1)) by applys prec_typing_regular PTyp.
      apply wf_ctx_typ...
  - Case "typing_tabs".
    replace (exp_cv e1)
       with (exp_cv (subst_te Z P e1))
         by (symmetry; apply subst_te_fresh_exp_cv).
    pick fresh Y and apply prec_typing_tabs.
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
    apply prec_typing_box...
    assert (WfCR : wf_typ (Δ ++ [(Z, bind_sub Q)] ++ Γ) S (C # R)).
    { applys prec_typing_regular PTyp. }
    assert (WfC : wf_cse (Δ ++ [(Z, bind_sub Q)] ++ Γ) S C).
    { inversion WfCR... }
    apply (wf_cse_subst_tb _ _ Q Z P C)...
  - Case "typing_unbox".
    apply prec_typing_unbox...
    eapply wf_cse_subst_tb...
Qed.

Lemma prec_typing_through_open_ve_typing : forall Γ S (x y : atom) U e T,
  y ∉ (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  prec_typing ([(y, bind_typ U)] ++ Γ) S (open_ve e y (cse_fvar y)) T ->
  prec_typing Γ S x U ->
  prec_typing Γ S (open_ve e x (cse_fvar x)) T.
Proof with eauto*.
  intros * NotIn Typ xTyp.
  assert (WfCtx : wf_ctx ([(y, bind_typ U)] ++ Γ) S) by applys prec_typing_regular Typ.
  inversion WfCtx; subst.
  inversion xTyp; subst.
  (* destruct (typing_var_implies_binds_typ _ _ _ _ S xTyp) as [D [Q [Binds [xsubC [WfD [QsubR PureR]]]]]]. *)
  assert (Neq : x <> y).
  { enough (x ∈ dom Γ) by fsetdec.
    eapply binds_In, H8.
  }
  rewrite_env (map (subst_cb y (cse_fvar x)) ∅ ++ Γ).
  replace (open_ve e x (cse_fvar x))
     with (subst_ve y x (cse_fvar x) (open_ve e y (cse_fvar y)))
       by (rewrite <- subst_ve_intro; auto).
  replace T
     with (subst_ct y (cse_fvar x) T)
       by (rewrite <- subst_ct_fresh; auto).
  eapply prec_typing_through_subst_ve with (C := cse_fvar x) (R := R).
  - simpl in *...
  - eapply prec_typing_var...
Qed.

Lemma prec_typing_through_open_ve_typing_open : forall Γ S (x y : atom) U e T,
  y ∉ (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  prec_typing ([(y, bind_typ U)] ++ Γ) S (open_ve e y (cse_fvar y)) (open_ct T (cse_fvar y)) ->
  prec_typing Γ S x U ->
  prec_typing Γ S (open_ve e x (cse_fvar x)) (open_ct T (cse_fvar x)).
Proof with eauto*.
  intros * NotIn PTyp xPTyp.
  assert (WfCtx : wf_ctx ([(y, bind_typ U)] ++ Γ) S) by applys prec_typing_regular PTyp.
  inversion WfCtx; subst.
  inversion xPTyp; subst.
  assert (Neq : x <> y).
  { enough (x ∈ dom Γ) by fsetdec.
    eapply binds_In, H8.
  }
  rewrite_env (map (subst_cb y (cse_fvar x)) ∅ ++ Γ).
  replace (open_ve e x (cse_fvar x))
     with (subst_ve y x (cse_fvar x) (open_ve e y (cse_fvar y)))
       by (rewrite <- subst_ve_intro; auto).
  replace (open_ct T (cse_fvar x))
     with (subst_ct y (cse_fvar x) (open_ct T (cse_fvar y)))
       by (rewrite <- subst_ct_intro; auto).
  eapply prec_typing_through_subst_ve with (C := cse_fvar x) (R := R)...
Qed.

Lemma prec_typing_through_open_te : forall Γ S (Y : atom) e T P Q,
  Y ∉ (fv_tt T `u`A fv_ct T `u`A fv_te e `u`A fv_ce e) ->
  prec_typing ([(Y, bind_sub Q)] ++ Γ) S (open_te e Y) (open_tt T Y) ->
  sub Γ S P Q ->
  prec_typing Γ S (open_te e P) (open_tt T P).
Proof with eauto*.
  intros * NotIn Typ Sub.
  rewrite_env (map (subst_tb Y P) ∅ ++ Γ).
  replace (open_te e P)
     with (subst_te Y P (open_te e Y))
     by (symmetry; apply subst_te_intro; clear - NotIn; fsetdec).
  replace (open_tt T P)
     with (subst_tt Y P (open_tt T Y))
     by (symmetry; apply subst_tt_intro; clear - NotIn; fsetdec).
  apply prec_typing_through_subst_te with (Q := Q)...
Qed.

