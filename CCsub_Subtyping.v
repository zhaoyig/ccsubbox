Require Import Coq.Program.Equality.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.

(** **************************************** **)
(** Properties of the subtyping relation     **)
(** **************************************** **)

(* ********************************************************************** *)
(** ** Reflexivity (1) *)
Lemma sub_reflexivity : forall Γ S T,
  wf_store_ctx S ->
  wf_ctx Γ S ->
  wf_typ Γ S T ->
  sub Γ S T T.
Proof with eauto using subcapt_reflexivity, wf_typ_weakening.
  intros *.
  intros WfS Ok Wf.
  induction Wf...
  - apply sub_arr with (L := L `union`A EnvImpl.dom Γ)...
    all: inversion Wf...
    pose (CRRefl := IHWf WfS Ok).
    inversion CRRefl...
  - apply sub_all with (L := L `union`A EnvImpl.dom Γ)...
Qed.

(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)

(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma sub_weakening : forall Γ Θ Δ S R T,
  sub (Δ ++ Γ) S R T ->
  wf_ctx (Δ ++ Θ ++ Γ) S ->
  sub (Δ ++ Θ ++ Γ) S R T.
Proof with simpl_env; eauto using wf_typ_weakening, subcapt_weakening, wf_cse_weakening.
  intros * Sub Ok.
  remember (Δ ++ Γ).
  generalize dependent Δ.
  induction Sub; intros Δ Ok EQ; subst...
  (* - Case sub_arr. *)
  - pick fresh y and apply sub_arr...
    rewrite <- app_assoc.
    rename select (forall x : atom, x ∉ L -> forall Δ0 : ctx, [(x, bind_typ (C2 # R2))] ++ _ = _ -> _) into IH.
    apply IH...
    apply wf_ctx_typ...
  (* - Case sub_all. *)
  - pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    rename select (forall X : atom, X ∉ L -> forall Δ0 : ctx, [(X, bind_sub R2)] ++ _ = _ -> _) into IH.
    apply IH...
    apply wf_ctx_sub...
Qed.

Lemma sub_weakening_store : forall Γ S1 S2 S3 T U,
  sub Γ (S1 ++ S3) T U ->
  wf_store_ctx (S1 ++ S2 ++ S3) ->
  sub Γ (S1 ++ S2 ++ S3) T U.
Proof with eauto using
  wf_ctx_weakening_store,
  wf_typ_weakening_store,
  subcapt_weakening_store.
  intros * Sub Ok.
  dependent induction Sub...
Qed.

(* ********************************************************************** *)
(** ** Strengthening (3) *)

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Definition transitivity_on Q := forall Γ S R T,
  sub Γ S R Q ->
  sub Γ S Q T ->
  sub Γ S R T.

Lemma subcapt_narrowing_typ : forall Δ Γ S x CP P CQ Q R T,
  subcapt (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ) S R T ->
  sub Γ S (CP # P) (CQ # Q) ->
  subcapt (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) S R T.
Proof with eauto using wf_cse_narrowing_typ, wf_ctx_narrowing_typ.
  intros * SsubT PsubQ.
  remember (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ).
  generalize dependent Δ.
  induction SsubT; intros Δ EQ; subst...
  destruct (X == x); subst...
  - analyze_binds H... inversion BindsTacVal.
    rewrite H0 in SsubT.
    apply (subcapt_trans_var CP S (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) Q0 x P).
    auto.
    inversion PsubQ; subst.
    assert (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ = Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ ) by reflexivity.
    specialize (IHSsubT PsubQ Δ H).
    assert (subcapt (Δ ++ ([(x, bind_typ (CP # P))]) ++ Γ) S CP CQ).
    {
      rewrite_env (nil ++ (Δ ++ [(x, bind_typ (CP # P))]) ++ Γ).
      apply (subcapt_weakening Γ (Δ ++ [(x, bind_typ (CP # P))]) nil CP CQ).
      simpl. exact H7.
      simpl. rewrite app_assoc.
      apply (proj1 (proj2 (subcapt_regular (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) CQ Q0 S IHSsubT))).
    }
    apply subcapt_transitivity with (Q := CQ)...
Qed.

Lemma subcapt_narrowing : forall Δ Γ S Z P Q C1 C2,
  sub Γ S P Q ->
  transitivity_on Q ->
  wf_ctx (Δ ++ [(Z, bind_sub P)] ++ Γ) S ->
  subcapt (Δ ++ [(Z, bind_sub Q)] ++ Γ) S C1 C2 ->
  subcapt (Δ ++ [(Z, bind_sub P)] ++ Γ) S C1 C2.
Proof with eauto 6 using wf_cse_narrowing, wf_ctx_narrowing.
  intros * SubPQ TransQ WfE SubCap.
  dependent induction SubCap...
  - analyze_binds H...
Qed.

Lemma sub_narrowing_aux : forall Q Δ Γ Z P R T S,
  transitivity_on Q ->
  sub (Δ ++ [(Z, bind_sub Q)] ++ Γ) S R T ->
  pure_type P ->
  sub Γ S P Q ->
  sub (Δ ++ [(Z, bind_sub P)] ++ Γ) S R T.
Proof with simpl_env;
           eauto using wf_typ_ignores_sub_bindings,
                       wf_ctx_narrowing,
                       wf_cse_narrowing,
                       subcapt_narrowing.
  intros * TransQ SsubT PureP PsubQ.
  remember (Δ ++ [(Z, bind_sub Q)] ++ Γ).
  assert (PureQ : pure_type Q) by (apply (sub_pure_type _ _ _ _ PsubQ), PureP).
  generalize dependent Δ.
  induction SsubT; intros Δ EQ; subst...
  (* - Case sub_trans_tvar. *)
  - destruct (X == Z); subst.
    (* + SCase "X = Z". *)
    + apply (sub_trans_tvar P).
      * apply binds_app_3.
        apply binds_app_2. auto.
      * apply TransQ.
        (* -- SSCase "{} # P <: {} # Q". *)
        -- forwards: IHSsubT Δ.
           1: congruence.
           simpl_env in *...
           rewrite_env (∅ ++ (Δ ++ [(Z, bind_sub P)]) ++ Γ).
           apply sub_weakening...
        (* -- SSCase "{} # Q <: T". *)
        -- rename select (binds Z _ _) into Binds.
           assert (bind_sub Q = bind_sub U). {
            admit.
           }
           (* binds_get Binds... *)
           inversion select (bind_sub _ = bind_sub _); subst...
    (* + SCase "X <> Z". *)
    + forwards: IHSsubT Δ.
      1: congruence.
      simpl_env in *...
      apply (sub_trans_tvar U)...
  (* - Case "sub_arr". *)
  - pick fresh Y and apply sub_arr...
    rewrite <- app_assoc. (*Formerly rewrite_parenthesise_binding*)
    rename select (forall x : atom, x ∉ L -> sub Γ S P Q -> forall Δ0 : ctx, [(x, bind_typ (C2 # R2))] ++ _ = _ -> _) into IH.
    eapply IH...
  (* - Case "sub_all". *)
  - pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    rename select (forall X : atom, X ∉ L -> sub Γ S P Q -> forall Δ0 : ctx, [(X, bind_sub R2)] ++ _ = _ -> _) into IH.
    eapply IH...
Admitted.

Lemma sub_narrowing_typ_aux : forall CQ Q Δ Γ x CP P R T S,
  sub (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ) S R T ->
  sub Γ S (CP # P) (CQ # Q) ->
  sub (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) S R T.
Proof with simpl_env;
           eauto using wf_typ_ignores_typ_bindings,
                       wf_ctx_narrowing_typ,
                       subcapt_narrowing_typ,
                       wf_cse_narrowing_typ.
  intros * SsubT PsubQ.
  remember (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ).
  generalize dependent Δ.
  induction SsubT; intros Δ EQ; subst...
  (* - Case "sub_trans_tvar". *)
  - apply sub_trans_tvar with (U := U)...
    analyze_binds H.
  (* - Case "sub_arr". *)
  - pick fresh Y and apply sub_arr...
    rewrite <- app_assoc.
    rename select (forall x0 : atom, x0 ∉ L -> sub Γ S (CP # P) (CQ # Q) -> forall Δ0 : ctx, [(x0, bind_typ (C2 # R2))] ++ _ = _ -> _) into IH.
    eapply IH...
  - pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    rename select (forall X : atom, X ∉ L -> sub Γ S (CP # P) (CQ # Q) -> forall Δ0 : ctx, [(X, bind_sub R2)] ++ _ = _ -> _) into IH.
    eapply IH...
Qed.

Lemma sub_transitivity_mut :
     (forall Q, type Q -> transitivity_on Q)
  /\ (forall Q, pure_type Q -> transitivity_on Q).
Proof with eauto using subcapt_transitivity.
  Ltac inductionThenInversion Rel1 Rel2 :=
    induction Rel1; try discriminate; subst; intros T' Rel2; inversion Rel2; subst.
  apply type_mutind; unfold transitivity_on; eauto.
  (* - Case "type_capt". *)
  - intros * PC PR IH * SsubQ QsubT.
    dependent induction QsubT; subst.
    (* + SCase "sub_capt". *)
    + inversion SsubQ; subst.
      (* * SSCase "sub_trans_tvar". *)
      * contradict SsubQ; intros XsubCR.
        assert (PureCR : pure_type (C # R))
            by (applys sub_pure_type XsubCR; auto).
        inversion PureCR.
      (* * SSCase "sub_capt". *)
      * apply sub_capt...
    (* + SCase "sub_top". *)
    + inversion select (pure_type (_ # _)).
  (* - Case "type_var". *)
  - intros * SsubQ QsubT.
    dependent induction SsubQ; eauto.
  (* - Case "type_top". *)
  - intros * SsubQ QsubT. dependent induction SsubQ; inversion QsubT; intros; eauto.
  (* - Case "type_arr". *)
  - intros * TypeS IH1 TypeT * IH2 * SsubQ QsubT.
    dependent induction SsubQ; inversion QsubT; intros.
    (* + SCase "sub_trans_tvar / sub_top". *)
    + apply sub_top...
    (* + SCase "sub_trans_tvar / sub_arr". *)
    + subst. eapply sub_trans_tvar...
    (* + SCase "sub_arr / sub_top". *)
    + subst.
      rename select (forall x : atom, x ∉ L0 -> sub _ _ _ _) into T1subT2.
      apply sub_top...
      * econstructor...
        intros x xNotIn.
        specialize (T1subT2 x xNotIn).
        rewrite_nil_concat.
        eapply wf_typ_ignores_typ_bindings.
        applys sub_regular T1subT2.
      * pick fresh x and apply type_arr...
        eapply type_from_wf_typ.
        specialize (T1subT2 x ltac:(fsetdec)).
        applys sub_regular T1subT2.
    (* + SCase "sub_arr / sub_arr". *)
    + subst. assert (IH : sub Γ S (C3 # R3) (C1 # R1)). {
        apply IH1...
      }
      pick fresh x and apply sub_arr; try auto.
      * inversion IH...
      * inversion IH...
      * rename select (forall x : atom, x ∉ L0 -> sub ([(x, bind_typ (C2 # R2))] ++ _) _ _ _) into T1subT2.
        specialize (T1subT2 x ltac:(fsetdec)).
        rename select (forall x : atom, x ∉ L1 -> sub ([(x, bind_typ (C3 # R3))] ++ _) _ _ _) into T2subT3.
        specialize (T2subT3 x ltac:(fsetdec)).
        apply IH2 with (X := x); [fsetdec | | auto].
        rewrite_nil_concat.
        apply sub_narrowing_typ_aux with (CQ := C2) (Q := R2)...
  (* - Case "type_all". *)
  - intros * TypeS IH1 TypeT * IH2 * SsubQ QsubT.
    dependent induction SsubQ; inversion QsubT; subst.
    (* + SCase "sub_trans_tvar / sub_top". *)
    + apply sub_top...
    (* + SCase "sub_trans_tvar / sub_all". *)
    + eapply sub_trans_tvar...
    (* + SCase "sub_all / sub_top". *)
    + rename select (forall x : atom, x ∉ L0 -> sub _ _ _ _) into T1subT2.
      apply sub_top...
      * econstructor...
        intros x xNotIn.
        specialize (T1subT2 x xNotIn).
        rewrite_nil_concat.
        eapply wf_typ_ignores_sub_bindings.
        applys sub_regular T1subT2.
      * econstructor...
        intros x xNotIn.
        specialize (T1subT2 x xNotIn).
        eapply type_from_wf_typ.
        applys sub_regular T1subT2.
    (* + SCase "sub_all / sub_all". *)
    + pick fresh X and apply sub_all; try auto.
      * rename select (forall x : atom, x ∉ L0 -> sub _ _ _ _) into T1subT2.
        specialize (T1subT2 X ltac:(fsetdec)).
        rename select (forall x : atom, x ∉ L1 -> sub _ _ _ _) into T2subT3.
        specialize (T2subT3 X ltac:(fsetdec)).
        apply IH2 with (X := X); [fsetdec | | auto].
        rewrite_nil_concat.
        eapply sub_narrowing_aux with (Q := R)...
  (* - Case "type_box". *)
  - intros * TypeT IH * SsubQ QsubT.
    dependent induction SsubQ; inversion QsubT; subst; eauto.
Qed.

Lemma sub_transitivity : forall Q Γ R T S,
  type Q ->
  sub Γ S R Q ->
  sub Γ S Q T ->
  sub Γ S R T.
Proof with eauto.
  intros.
  apply (proj1 sub_transitivity_mut Q)...
Qed.

Lemma sub_narrowing : forall Q Γ Δ Z P R T S,
  pure_type P ->
  sub Γ S P Q ->
  sub (Δ ++ [(Z, bind_sub Q)] ++ Γ) S R T ->
  sub (Δ ++ [(Z, bind_sub P)] ++ Γ) S R T.
Proof with auto.
  intros.
  eapply sub_narrowing_aux; eauto; unfold transitivity_on; intros.
  eapply sub_transitivity with (Q := Q)...
Qed.

Lemma sub_narrowing_typ : forall Γ Δ x CP P CQ Q R T S,
  sub (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ) S R T ->
  sub Γ S (CP # P) (CQ # Q) ->
  sub (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) S R T.
Proof with eauto.
  intros * SsubT PsubQ.
  eapply sub_narrowing_typ_aux; eauto.
Qed.
