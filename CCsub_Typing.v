Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)

(* ********************************************************************** *)
(** ** Weakening (5) *)
Lemma typing_weakening : forall Γ Θ Δ e T,
  (Δ ++ Γ) ⊢ e : T ->
  (Δ ++ Θ ++ Γ) ⊢ wf ->
  (Δ ++ Θ ++ Γ) ⊢ e : T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ,
                       sub_weakening,
                       subcapt_weakening.
  intros * Typ.
  remember (Δ ++ Γ).
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
    apply wf_cset_weakening... 
Qed.

(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q Δ Γ X P e T,
  Γ ⊢ P <: Q ->
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ e : T ->
  (Δ ++ [(X, bind_sub P)] ++ Γ) ⊢ e : T.
Proof with eauto using wf_env_narrowing, wf_typ_ignores_sub_bindings, sub_narrowing, subcapt_narrowing.
  intros * PsubQ Typ.
  assert (PureP : pure_type P).
  { enough (PureQ : pure_type Q) by (applys sub_pure_type PsubQ; eauto* ).
    forwards (WfEnv & _): typing_regular Typ.
    apply wf_env_tail in WfEnv.
    inversion WfEnv...
  }
  assert (WfEnv : wf_env (Δ ++ [(X, bind_sub P)] ++ Γ)). {
    apply wf_env_narrowing with (V := Q)...
  }
  remember (Δ ++ [(X, bind_sub Q)] ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ WfEnv; subst.
  - Case "typing_var".
    binds_cases H0...
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
    apply wf_env_typ...
    apply wf_typ_ignores_sub_bindings with (V := Q).
    applys typing_regular Typ.
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    rewrite <- concat_assoc.
    apply H2...
    apply wf_env_sub...
  - Case "typing_tapp".
    eapply typing_tapp...
  - Case "typing_box".
    apply typing_box...
    apply wf_cset_narrowing with (V := Q)...
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cset_narrowing...
  - Case "typing_sub".
    apply typing_sub with (S := S)...
Qed.

Lemma typing_narrowing_typ : forall D Q Γ Δ X C P e T,
  (Δ ++ [(X, bind_typ (D # Q))] ++ Γ) ⊢ e : T ->
  Γ ⊢ (C # P) <: (D # Q) ->
  (Δ ++ [(X, bind_typ (C # P))] ++ Γ) ⊢ e : T.
Proof with eauto*.
  intros * Typ Sub.
  assert (CsubD_PsubQ_WfC_WfD_PureP_PureQ : Γ ⊢ₛ C <: D /\ Γ ⊢ P <: Q /\ Γ ⊢ₛ C wf /\ Γ ⊢ₛ D wf /\ pure_type P /\ pure_type Q).
  { dependent induction Sub... }
  destruct CsubD_PsubQ_WfC_WfD_PureP_PureQ as [CsubD [PsubQ [WfC [WfD [PureP PureQ]]]]].
  dependent induction Typ.
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds; simpl_env in *.
    + eapply typing_var...
      eapply wf_env_narrowing_typ...
    + inversion select (bind_typ _ = bind_typ _); subst.
      apply typing_sub with (S := cse_fvar x # P).
      * apply typing_var with (C := C)...
        eapply wf_env_narrowing_typ...
      * apply sub_capt...
        -- apply subcapt_reflexivity...
           apply wf_env_narrowing_typ with (C1 := D) (R1 := Q)...
        -- rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (C # P))]) ++ Γ).
           apply sub_weakening...
           simpl_env.
           eapply wf_env_narrowing_typ...
    + apply typing_var with (C := C0)...
      eapply wf_env_narrowing_typ...
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
    apply wf_cset_narrowing_typ with (C1 := D) (R1 := Q)...
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cset_narrowing_typ...
  - Case "typing_sub".
    apply typing_sub with (S := S)...
    eapply sub_narrowing_typ...
Qed.

(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall Γ S1 e1 T,
  Γ ⊢ (λ (S1) e1) : T ->
  forall U1 U2 C, Γ ⊢ T <: (C # (∀ (U1) U2)) ->
     Γ ⊢ U1 <: S1
  /\ exists S2, exists L, forall x, x ∉ L ->
    ([(x, bind_typ S1)] ++ Γ) ⊢ (open_ve e1 x (cse_fvar x)) : (open_ct S2 (cse_fvar x)) /\
    ([(x, bind_typ S1)] ++ Γ) ⊢ (open_ct U2 (cse_fvar x)) wf /\
    ([(x, bind_typ U1)] ++ Γ) ⊢ (open_ct S2 (cse_fvar x)) <: (open_ct U2 (cse_fvar x)).
Proof with auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_abs".
    inversion Sub; subst.
    inversion select (_ ⊢ _ <: _); subst.
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

Lemma typing_inv_tabs : forall Γ S1 e1 T,
  Γ ⊢ (Λ [S1] e1) : T ->
  forall U1 U2 C, Γ ⊢ T <: (C # (∀ [U1] U2)) ->
     Γ ⊢ U1 <: S1
  /\ exists S2, exists L, forall X, X ∉ L ->
       ([(X, bind_sub U1)] ++ Γ) ⊢ (open_te e1 X) : (open_tt S2 X) /\
       ([(X, bind_sub U1)] ++ Γ) ⊢ (open_tt S2 X) <: (open_tt U2 X).
Proof with simpl_env; auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_tabs".
    inversion Sub; subst.
    inversion select (_ ⊢ _ <: _); subst.
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

Lemma typing_inv_let : forall Γ e k T,
  Γ ⊢ (let= e in k) : T ->
  exists C R,
       Γ ⊢ e : (C # R)
    /\ exists L, forall x, x ∉ L ->
         ([(x, bind_typ (C # R))] ++ Γ) ⊢ (open_ve k x (cse_fvar x)) : T.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
  destruct (IHTyp e k ltac:(reflexivity)) as [C [R [eTyp [L kTyp]]]].
  exists C, R.
  split...
  exists (L `u`A dom Γ).
  intros y NotIn.
  specialize (kTyp y ltac:(clear - NotIn; fsetdec)).
  apply typing_sub with (S := S)...
  rewrite_env (∅ ++ [(y, bind_typ (C # R))] ++ Γ).
  apply sub_weakening...
Qed.
