Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)

(* ********************************************************************** *)
(** ** Weakening (5) *)
Lemma typing_weakening : forall Γ Θ Δ e T S,
  typing (Δ ++ Γ) S e T ->
  wf_ctx (Δ ++ Θ ++ Γ) S ->
  typing (Δ ++ Θ ++ Γ) S e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_ctx_typ,
                       sub_weakening,
                       subcapt_weakening.
  intros * Typ. remember (Δ ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ Ok; subst...
  - Case "typing_abs".
    pick fresh X and apply typing_abs...
    lapply (H0 X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply H1...
  - Case "typing_let".
    pick fresh X and apply typing_let...
    lapply (H X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply (H0 X)...
  - Case "typing_tabs".
    pick fresh X and apply typing_tabs...
    lapply (H1 X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply H2...
  - Case "typing_box".
    apply typing_box...
    simpl_env in H.
    assert (Δ ++ Γ = Δ ++ Γ) by reflexivity.
    specialize (IHTyp Δ H0 Ok).
    inversion IHTyp...
  - Case "typing_unbox".
    apply typing_unbox...
    apply wf_cse_weakening... 
Qed.

(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q Δ Γ X P e T S,
  sub Γ S P Q ->
  typing (Δ ++ [(X, bind_sub Q)] ++ Γ) S e T ->
  typing (Δ ++ [(X, bind_sub P)] ++ Γ) S e T.
Proof with eauto using wf_ctx_narrowing, wf_typ_ignores_sub_bindings, sub_narrowing, subcapt_narrowing.
  intros * PsubQ Typ.
  assert (PureP : pure_type P).
  { enough (PureQ : pure_type Q) by (applys sub_pure_type PsubQ; eauto* ).
    forwards (_ & WfCtx & _): typing_regular Typ.
    apply wf_ctx_tail in WfCtx.
    inversion WfCtx...
  }
  assert (WfCtx : wf_ctx (Δ ++ [(X, bind_sub P)] ++ Γ) S). {
    apply wf_ctx_narrowing with (V := Q)...
  }
  remember (Δ ++ [(X, bind_sub Q)] ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ WfCtx; subst.
  - Case "typing_var".
    binds_cases H0...
  - Case "typing_loc".
    apply typing_loc with (R := R) (C := C)...
  - Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite <- concat_assoc.
    apply H1...
    econstructor...
  - Case "typing_app".
    eapply typing_app...
  - Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite_parenthesise_binding.
    apply H0...
    apply wf_ctx_typ...
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    rewrite <- concat_assoc.
    apply H2...
    apply wf_ctx_sub...
  - Case "typing_tapp".
    eapply typing_tapp...
  - Case "typing_box".
    apply typing_box...
    apply wf_cse_narrowing with (V := Q)...
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cse_narrowing...
  - Case "typing_sub".
    apply typing_sub with (R := R)...
Qed.

Lemma typing_narrowing_typ : forall D Q Γ Δ X C P e T S,
  typing (Δ ++ [(X, bind_typ (D # Q))] ++ Γ) S e T ->
  sub Γ S (C # P) (D # Q) ->
  typing (Δ ++ [(X, bind_typ (C # P))] ++ Γ) S e T.
Proof with eauto*.
  intros * Typ Sub.
  assert (CsubD_PsubQ_WfC_WfD_PureP_PureQ : subcapt Γ S C D /\ sub Γ S P Q /\ wf_cse Γ S C /\ wf_cse Γ S D /\ pure_type P /\ pure_type Q).
  { dependent induction Sub... }
  destruct CsubD_PsubQ_WfC_WfD_PureP_PureQ as [CsubD [PsubQ [WfC [WfD [PureP PureQ]]]]].
  dependent induction Typ.
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds; simpl_env in *.
    + eapply typing_var...
      eapply wf_ctx_narrowing_typ...
    + inversion select (bind_typ _ = bind_typ _); subst.
      apply typing_sub with (R := cse_fvar x # P).
      * apply typing_var with (C := C)...
        eapply wf_ctx_narrowing_typ...
      * apply sub_capt...
        -- apply subcapt_reflexivity...
           apply wf_ctx_narrowing_typ with (C1 := D) (R1 := Q)...
        -- rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (C # P))]) ++ Γ).
           apply sub_weakening...
           simpl_env.
           eapply wf_ctx_narrowing_typ...
    + apply typing_var with (C := C0)...
      eapply wf_ctx_narrowing_typ...
  - Case "typing_loc".
    apply typing_loc with (R := R) (C := C0)...
    eapply wf_ctx_narrowing_typ...
  - Case "typing_abs".
    pick fresh y and apply typing_abs...
    + simpl_env in *.
      eapply wf_typ_ignores_typ_bindings...
    + rewrite_parenthesise_binding.
      rename select (forall x : atom, x ∉ L -> forall (D0 : cse), _) into IH.
      eapply IH...
  - Case "typing_app".
    eapply typing_app...
  - Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite_parenthesise_binding.
    rename select (forall x : atom, x ∉ L -> forall (D0 : cse), _) into IH.
    eapply IH...
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    + simpl_env in *.
      eapply wf_typ_ignores_typ_bindings...
    + rewrite_parenthesise_binding.
      rename select (forall X0 : atom, X0 ∉ L -> forall (D0 : cse), _) into IH.
      eapply IH...
  - Case "typing_tapp".
    eapply typing_tapp...
    eapply sub_narrowing_typ...
  - Case "typing_box".
    apply typing_box...
    apply wf_cse_narrowing_typ with (C1 := D) (R1 := Q)...
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cse_narrowing_typ...
  - Case "typing_sub".
    apply typing_sub with (R := R)...
    eapply sub_narrowing_typ...
Qed.

(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall Γ S1 e1 T S,
  typing Γ S (λ (S1) e1) T ->
  forall U1 U2 C, sub Γ S T (C # (∀ (U1) U2)) ->
     sub Γ S U1 S1
  /\ exists S2, exists L, forall x, x ∉ L ->
    typing ([(x, bind_typ S1)] ++ Γ) S (open_ve e1 x (cse_fvar x)) (open_ct S2 (cse_fvar x)) /\
    wf_typ ([(x, bind_typ S1)] ++ Γ) S (open_ct U2 (cse_fvar x)) /\
    sub ([(x, bind_typ U1)] ++ Γ) S (open_ct S2 (cse_fvar x)) (open_ct U2 (cse_fvar x)).
Proof with auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_abs".
    inversion Sub; subst.
    inversion select (sub _ _ _ _); subst.
    split...
    exists T1.
    exists (L `u`A L0).
    intros y ?.
    rename select (forall x : atom, x ∉ L0 -> _) into Sub'.
    specialize (Sub' y ltac:(fsetdec)).
    repeat split...
    rewrite_nil_concat.
    eapply wf_typ_ignores_typ_bindings.
    applys sub_regular Sub'.
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall Γ S1 e1 T S,
  typing Γ S (Λ [S1] e1) T ->
  forall U1 U2 C, sub Γ S T (C # (∀ [U1] U2)) ->
     sub Γ S U1 S1
  /\ exists S2, exists L, forall X, X ∉ L ->
    typing ([(X, bind_sub U1)] ++ Γ) S (open_te e1 X) (open_tt S2 X) /\
    sub ([(X, bind_sub U1)] ++ Γ) S (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_tabs".
    inversion Sub; subst.
    inversion select (sub _ _ _ _); subst.
    split...
    exists T1.
    exists (L `union` L0).
    intros Y ?.
    repeat split...
    rewrite_nil_concat.
    eapply typing_narrowing with (Q := S1)...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

Lemma typing_inv_let : forall Γ e k T S,
  typing Γ S (let= e in k) T ->
  exists C R,
    typing Γ S e (C # R)
    /\ exists L, forall x, x ∉ L ->
      typing ([(x, bind_typ (C # R))] ++ Γ) S (open_ve k x (cse_fvar x)) T.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
  destruct (IHTyp e k ltac:(reflexivity)) as [C [R0 [eTyp [L kTyp]]]].
  exists C, R0.
  split...
  exists (L `u`A dom Γ).
  intros y NotIn.
  specialize (kTyp y ltac:(clear - NotIn; fsetdec)).
  apply typing_sub with (R := R)...
  rewrite_env (∅ ++ [(y, bind_typ (C # R0))] ++ Γ).
  apply sub_weakening...
Qed.
