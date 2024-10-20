Require Import Coq.Program.Equality.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.

(** **************************************** **)
(** Properties of the subtyping relation     **)
(** **************************************** **)

(* ********************************************************************** *)
(** ** Reflexivity (1) *)
Lemma sub_reflexivity : forall Γ T,
  Γ ⊢ wf ->
  Γ ⊢ T wf ->
  Γ ⊢ T <: T.
Proof with eauto using subcapt_reflexivity, wf_typ_weakening.
  intros *.
  intros Ok Wf.
  induction Wf...
  - apply sub_arr with (L := L `u`A dom Γ)...
    all: inversion Wf...
    pose (CRRefl := IHWf Ok).
    inversion CRRefl...
  - apply sub_all with (L := L `u`A dom Γ)...
Qed.

(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)

(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma sub_weakening : forall Γ Θ Δ S T,
  (Δ ++ Γ) ⊢ S <: T ->
  (Δ ++ Θ ++ Γ) ⊢ wf ->
  (Δ ++ Θ ++ Γ) ⊢ S <: T.
Proof with simpl_env; eauto using wf_typ_weakening, subcapt_weakening, wf_cset_weakening.
  intros * Sub Ok.
  remember (Δ ++ Γ).
  generalize dependent Δ.
  induction Sub; intros Δ Ok EQ; subst...
  - Case "sub_arr".
    pick fresh y and apply sub_arr...
    rewrite <- concat_assoc.
    rename select (forall x : atom, x ∉ L -> forall Δ0 : env, [(x, bind_typ (C2 # R2))] ++ _ = _ -> _) into IH.
    apply IH...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    rename select (forall X : atom, X ∉ L -> forall Δ0 : env, [(X, bind_sub R2)] ++ _ = _ -> _) into IH.
    apply IH...
Qed.

(* ********************************************************************** *)
(** ** Strengthening (3) *)

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Definition transitivity_on Q := forall Γ S T,
  Γ ⊢ S <: Q -> Γ ⊢ Q <: T -> Γ ⊢ S <: T.

Lemma subcapt_narrowing_typ : forall Δ Γ x CP P CQ Q S T,
  (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ) ⊢ₛ S <: T ->
  Γ ⊢ (CP # P) <: (CQ # Q) ->
  (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) ⊢ₛ S <: T.
Proof with eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ.
  intros * SsubT PsubQ.
  remember (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ).
  generalize dependent Δ.
  induction SsubT; intros Δ EQ; subst...
  destruct (X == x); subst...
  - binds_cases H... inversion H0.
    rewrite H2 in SsubT.
    apply (subcset_trans_var CP (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) Q0 x P).
    auto.
    inversion PsubQ; subst.
    assert (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ = Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ ) by reflexivity.
    specialize (IHSsubT Δ H1).
    assert ((Δ ++ ([(x, bind_typ (CP # P))]) ++ Γ) ⊢ₛ CP <: CQ). 
    {
      rewrite_env (nil ++ (Δ ++ [(x, bind_typ (CP # P))]) ++ Γ).
      apply (subcapt_weakening Γ (Δ ++ [(x, bind_typ (CP # P))]) nil  CP CQ).
      simpl. exact H8.
      simpl. rewrite concat_assoc.
      apply (subcapt_env_wf (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) CQ Q0) in IHSsubT. exact IHSsubT.
    }
    apply subcapt_transitivity with (Q := CQ)...
  - binds_cases H...
Qed.

Lemma subcapt_narrowing : forall Δ Γ Z P Q C1 C2,
  Γ ⊢ P <: Q ->
  transitivity_on Q ->
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ wf ->
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ₛ C1 <: C2 ->
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ₛ C1 <: C2.
Proof with eauto 6 using wf_cset_narrowing, wf_env_narrowing.
  intros * SubPQ TransQ WfE SubCap.
  dependent induction SubCap...
  - binds_cases H...
Qed.

Lemma sub_narrowing_aux : forall Q Δ Γ Z P S T,
  transitivity_on Q ->
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ S <: T ->
  pure_type P ->
  Γ ⊢ P <: Q ->
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ S <: T.
Proof with simpl_env;
           eauto using wf_typ_ignores_sub_bindings,
                       wf_env_narrowing,
                       wf_cset_narrowing,
                       subcapt_narrowing.
  intros * TransQ SsubT PureP PsubQ.
  remember (Δ ++ [(Z, bind_sub Q)] ++ Γ).
  assert (PureQ : pure_type Q) by (apply (sub_pure_type _ _ _ PsubQ), PureP).
  generalize dependent Δ.
  induction SsubT; intros Δ EQ; subst...
  - Case "sub_trans_tvar".
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_trans_tvar P).
      * apply binds_tail.
        apply binds_head; apply binds_singleton.
        eapply fresh_mid_head.
        apply ok_from_wf_env.
        applys sub_regular SsubT.
      * apply TransQ.
        -- SSCase "{} # P <: {} # Q".
           forwards: IHSsubT Δ.
           1: congruence.
           simpl_env in *.
           rewrite_env (∅ ++ (Δ ++ [(Z, bind_sub P)]) ++ Γ).
           apply sub_weakening...
        -- SSCase "{} # Q <: T".
          rename select (binds Z _ _) into Binds.
           binds_get Binds.
           inversion select (bind_sub _ = bind_sub _); subst...
    + SCase "X <> Z".
      forwards: IHSsubT Δ.
      1: congruence.
      simpl_env in *.
      apply (sub_trans_tvar U)...
  - Case "sub_arr".
    pick fresh Y and apply sub_arr...
    rewrite_parenthesise_binding.
    rename select (forall x : atom, x ∉ L -> forall Δ0 : env, [(x, bind_typ (C2 # R2))] ++ _ = _ -> _) into IH.
    eapply IH...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite_parenthesise_binding.
    rename select (forall X : atom, X ∉ L -> forall Δ0 : env, [(X, bind_sub R2)] ++ _ = _ -> _) into IH.
    eapply IH...
Qed.

Lemma sub_narrowing_typ_aux : forall CQ Q Δ Γ x CP P S T,
  (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ) ⊢ S <: T ->
  Γ ⊢ (CP # P) <: (CQ # Q) ->
  (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) ⊢ S <: T.
Proof with simpl_env;
           eauto using wf_typ_ignores_typ_bindings,
                       wf_env_narrowing_typ,
                       subcapt_narrowing_typ,
                       wf_cset_narrowing_typ.
  intros * SsubT PsubQ.
  remember (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ).
  generalize dependent Δ.
  induction SsubT; intros Δ EQ; subst...
  - Case "sub_trans_tvar".
    apply sub_trans_tvar with (U := U)...
    binds_cases H.
    + apply binds_tail...
    + apply binds_head...
  - Case "sub_arr".
    pick fresh Y and apply sub_arr...
    rewrite_parenthesise_binding.
    rename select (forall x0 : atom, x0 ∉ L -> forall Δ0 : env, [(x0, bind_typ (C2 # R2))] ++ _ = _ -> _) into IH.
    eapply IH...
  - pick fresh Y and apply sub_all...
    rewrite_parenthesise_binding.
    rename select (forall X : atom, X ∉ L -> forall Δ0 : env, [(X, bind_sub R2)] ++ _ = _ -> _) into IH.
    eapply IH...
Qed.

Lemma sub_transitivity_mut :
     (forall Q, type Q -> transitivity_on Q)
  /\ (forall Q, pure_type Q -> transitivity_on Q).
Proof with eauto using subcapt_transitivity.
  Ltac inductionThenInversion Rel1 Rel2 :=
    induction Rel1; try discriminate; subst; intros T' Rel2; inversion Rel2; subst.
  apply type_mutind; unfold transitivity_on; eauto.
  - Case "type_capt".
    intros * PC PR IH * SsubQ QsubT.
    dependent induction QsubT; subst.
    + SCase "sub_capt".
      inversion SsubQ; subst.
      * SSCase "sub_trans_tvar".
        contradict SsubQ; intros XsubCR.
        assert (PureCR : pure_type (C # R))
            by (applys sub_pure_type XsubCR; auto).
        inversion PureCR.
      * SSCase "sub_capt".
        apply sub_capt...
    + SCase "sub_top".
      inversion select (pure_type (_ # _)).
  - Case "type_var".
    intros * SsubQ QsubT.
    dependent induction SsubQ; eauto.
  - Case "type_top".
    intros * SsubQ QsubT. dependent induction SsubQ; inversion QsubT; intros; eauto.
  - Case "type_arr".
    intros * TypeS IH1 TypeT * IH2 * SsubQ QsubT.
    dependent induction SsubQ; inversion QsubT; intros.
    + SCase "sub_trans_tvar / sub_top".
      apply sub_top...
    + SCase "sub_trans_tvar / sub_arr". subst.
      eapply sub_trans_tvar...
    + SCase "sub_arr / sub_top". subst.
      rename select (forall x : atom, x ∉ L0 -> _ ⊢ _ <: _) into T1subT2.
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
    + SCase "sub_arr / sub_arr". subst.
      assert (IH : Γ ⊢ (C3 # R3) <: (C1 # R1)). {
        apply IH1...
      }
      pick fresh x and apply sub_arr; try auto.
      * inversion IH...
      * inversion IH...
      * rename select (forall x : atom, x ∉ L0 -> ([(x, bind_typ (C2 # R2))] ++ _) ⊢ _ <: _) into T1subT2.
        specialize (T1subT2 x ltac:(fsetdec)).
        rename select (forall x : atom, x ∉ L1 -> ([(x, bind_typ (C3 # R3))] ++ _) ⊢ _ <: _) into T2subT3.
        specialize (T2subT3 x ltac:(fsetdec)).
        apply IH2 with (X := x); [fsetdec | | auto].
        rewrite_nil_concat.
        apply sub_narrowing_typ_aux with (CQ := C2) (Q := R2)...
  - Case "type_all".
    intros * TypeS IH1 TypeT * IH2 * SsubQ QsubT.
    dependent induction SsubQ; inversion QsubT; subst.
    + SCase "sub_trans_tvar / sub_top".
      apply sub_top...
    + SCase "sub_trans_tvar / sub_all".
      eapply sub_trans_tvar...
    + SCase "sub_all / sub_top".
      rename select (forall x : atom, x ∉ L0 -> _ ⊢ _ <: _) into T1subT2.
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
    + SCase "sub_all / sub_all".
      pick fresh X and apply sub_all; try auto.
      * rename select (forall x : atom, x ∉ L0 -> _ ⊢ _ <: _) into T1subT2.
        specialize (T1subT2 X ltac:(fsetdec)).
        rename select (forall x : atom, x ∉ L1 -> _ ⊢ _ <: _) into T2subT3.
        specialize (T2subT3 X ltac:(fsetdec)).
        apply IH2 with (X := X); [fsetdec | | auto].
        rewrite_nil_concat.
        eapply sub_narrowing_aux with (Q := R)...
  - Case "type_box".
    intros * TypeT IH * SsubQ QsubT.
    dependent induction SsubQ; inversion QsubT; subst; eauto.
Qed.

Lemma sub_transitivity : forall Q Γ S T,
  type Q ->
  Γ ⊢ S <: Q ->
  Γ ⊢ Q <: T ->
  Γ ⊢ S <: T.
Proof with eauto*.
  intros.
  apply (proj1 sub_transitivity_mut Q)...
Qed.

Lemma sub_narrowing : forall Q Γ Δ Z P S T,
  pure_type P ->
  Γ ⊢ P <: Q ->
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ S <: T ->
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ S <: T.
Proof with auto.
  intros.
  eapply sub_narrowing_aux; eauto; unfold transitivity_on; intros.
  eapply sub_transitivity with (Q := Q)...
Qed.

Lemma sub_narrowing_typ : forall Γ Δ x CP P CQ Q S T,
  (Δ ++ [(x, bind_typ (CQ # Q))] ++ Γ) ⊢ S <: T ->
  Γ ⊢ (CP # P) <: (CQ # Q) ->
  (Δ ++ [(x, bind_typ (CP # P))] ++ Γ) ⊢ S <: T.
Proof with eauto*.
  intros * SsubT PsubQ.
  eapply sub_narrowing_typ_aux; eauto.
Qed.
