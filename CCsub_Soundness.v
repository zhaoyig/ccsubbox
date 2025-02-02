Require Import Coq.Program.Equality.
Require Import Lia.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.

Set Nested Proofs Allowed.

Hint Constructors store_typing eval_typing state_typing : core.

(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

(* Definition no_type_bindings (Γ : store_env) : Prop := *)
(*   forall X U, ~ Store.binds X (bind_sub U) Γ. *)

(* Should be true because of new definitions *)
(*
Lemma store_typing_no_type_bindings : forall S Γ,
  store_typing S Γ ->
  no_type_bindings Γ.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp.
  - easy.
  - intros X U Binds.
    binds_cases Binds.
    rename select (binds _ (bind_sub _) _) into Binds.
    applys IHStoreTyp Binds.
Qed.
*)

Lemma env_implies_value : forall S E l v,
  store_typing E S ->
  stores E l v ->
  value v.
Proof with eauto*.
  intros * StoreTyp Stores.
  induction StoreTyp; inversion Stores; subst.
  destruct (l ==== l0); subst...
Qed.

Lemma stores_preserves_typing : forall S E l v C P,
  store_typing E S ->
  stores E l v ->
  typing nil S l (C # P) ->
  exists D Q, typing nil S v (exp_cv v # Q)
         /\ Store.binds l (D # Q) S
         /\ subcapt nil S (exp_cv v) D
         /\ sub nil S Q P.
Proof with eauto*.
  intros * StoreTyp lStores.
  revert C P.
  induction StoreTyp as [|y D Q w E S StoreTyp IH w_value Typ NotIn]; intros C P Typ'; inversion lStores.
  destruct (l ==== y); subst.
  - Case "l = y".
    inversion select (Some _ = Some _); subst.
    destruct (values_have_precise_captures _ _ _ _ S w_value Typ) as [U [TypCVU CVUSubDQ]].
    exists D, Q.
    inversion CVUSubDQ; subst.
    repeat split...
    + inversion CVUSubDQ; subst...
      assert (typing nil S v (exp_cv v # Q)). {
        apply typing_sub with (R := exp_cv v # U).
        assumption.
        inversion CVUSubDQ; subst...
        apply sub_capt...
        apply subcapt_reflexivity...
      }
      rewrite_env (nil ++ [(y, D # Q)] ++ S).
      apply typing_weakening_store...
    + rewrite Store.cons_concat.
      apply Store.binds_head.
      apply Store.binds_singleton.
    + rewrite_env (nil ++ [(y, D # Q)] ++ S).
      apply subcapt_weakening_store...
    + eremember (C # P) as T.
      assert (Sub : sub nil ([(y, D # Q)] ++ S) T (C # P)). {
        rewrite <- HeqT.
        apply sub_reflexivity...
      }
      clear HeqT.
      dependent induction Typ'.
      * rename select (Store.binds _ _ _) into Binds.
        assert (C0 # R = D # Q). {
          apply Store.binds_mid_eq_cons with (x := y) (F := nil) (E := S)...
        }
        Store.binds_cases Binds.
        inversion H0; subst...
        inversion Sub...
      * eapply IHTyp'...
        apply sub_transitivity with (Q := T)...
  - Case "l <> y".
    destruct (typing_loc_implies_binds _ _ _ _ _ Typ') as [C' [R' [Binds Rest]]].
    assert (Binds' : Store.binds l (C' # R') S) by (eapply Store.binds_remove_mid_cons with (G := nil); eauto).
    assert (WfC'R' : wf_typ nil S (C' # R')) by (apply wf_typ_from_wf_store_ctx with (l := l); eauto).
    destruct (IH ltac:(assumption) C' R') as [D'' [Q'' [Typ'' [Binds'' [CVsubD'' Q''subR']]]]].
    + apply typing_sub with (R := cse_loc l # R').
      * apply typing_loc with (C := C')...
      * apply sub_capt; try inversion WfC'R'; subst...
        -- apply (subcapt_trans_loc _ C' _ _ _ R')...
           apply subcapt_reflexivity...
        -- apply sub_reflexivity...
    + assert (Eq : (C' # R') = (D'' # Q'')).
      { apply Store.binds_unique with (E := S) (x := l)... }
      symmetry in Eq; inversion Eq; subst.
      exists C', R'.
      repeat split...
      * rewrite_env (nil ++ [(y, D # Q)] ++ S).
        apply typing_weakening_store...
      * rewrite_env (nil ++ [(y, D # Q)] ++ S).
        apply subcapt_weakening_store...
Qed.

Lemma eval_typing_sub : forall Γ S K R1 R2 T1 T2,
  sub Γ S R2 R1 ->
  eval_typing Γ S K R1 T1 ->
  sub Γ S T1 T2 ->
  eval_typing Γ S K R2 T2.
Proof with eauto*.
  intros * R2SubR1 EvalTyp T1SubT2.
  revert R2 T2 R2SubR1 T1SubT2.
  induction EvalTyp; intros R4 T2 R2subC1R1 C2R2subT2.
  - Case "typing_eval_nil".
    rename select (sub Γ S (C1 # R1) (C2 # R2)) into C1R1subC2R2.
    destruct (proj1 (sub_capt_type _ _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst.
    destruct (proj2 (sub_capt_type _ _ _ _ R2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst.
    apply typing_eval_nil...
    apply sub_transitivity with (Q := C1 # R1)...
    apply sub_transitivity with (Q := C2 # R2)...
  - Case "typing_eval_cons".  
    destruct (proj1 (sub_capt_type _ _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst.
    destruct (proj2 (sub_capt_type _ _ _ _ R2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst.
    apply typing_eval_cons with (L := L) (C2 := C2) (R2 := R2)...
    + intros x xNotIn.
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
    + apply IHEvalTyp...
      apply sub_reflexivity...
      applys eval_typing_regular EvalTyp.
Qed.

Lemma eval_typing_weakening : forall Γ Δ Θ S E T U,
  eval_typing (Δ ++ Γ) S E T U ->
  wf_ctx (Δ ++ Θ ++ Γ) S ->
  eval_typing (Δ ++ Θ ++ Γ) S E T U.
Proof with eauto*.
  intros * EvalTyp WfCtx.
  induction EvalTyp.
  - Case "typing_eval_nil".
    apply typing_eval_nil...
    apply sub_weakening...
  - Case "typing_eval_cons".
    apply typing_eval_cons with (L := L `u`A dom (Δ ++ Θ ++ Γ)) (C2 := C2) (R2 := R2)...
    intros x xNotIn.
    rename select (forall x, x ∉ L -> typing _ _ _ _) into Typ.
    specialize (Typ x ltac:(fsetdec)).
    rewrite <- concat_assoc in Typ.
    apply typing_weakening with (Θ := Θ) in Typ.
    + apply Typ.
    + simpl_env.
      apply wf_ctx_typ...
      assert (WfCtx' : wf_ctx (([(x, bind_typ (C1 # R1))] ++ Δ) ++ Γ) S) by applys typing_regular Typ.
      inversion WfCtx'; subst.
      apply wf_typ_weakening...
Qed.

Lemma eval_typing_weakening_store : forall Γ S1 S2 S3 E T U,
  eval_typing Γ (S1 ++ S2) E T U ->
  wf_store_ctx (S1 ++ S3 ++ S2) ->
  eval_typing Γ (S1 ++ S3 ++ S2) E T U.
Proof with eauto*.
  intros * EvalTyp WfCtx.
  induction EvalTyp.
  - Case "typing_eval_nil".
    apply typing_eval_nil...
    apply sub_weakening_store...
  - Case "typing_eval_cons".
    apply typing_eval_cons with (L := L) (C2 := C2) (R2 := R2)...
    intros x xNotIn.
    specialize (H x xNotIn).
    apply typing_weakening_store with (S2 := S3) in H...
Qed.

Lemma store_typing_preserves_dom : forall E S,
  store_typing E S ->
  Store.dom E = Store.dom S.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp...
  repeat rewrite dom_concat; simpl.
  rewrite IHStoreTyp...
Qed.

Lemma typing_inv_app : forall Γ S (f l : loc) T,
  typing Γ S (f @ l) T ->
  exists C D Q U, typing Γ S f (C # (∀ (D # Q) U))
               /\ typing Γ S l (D # Q)
               /\ sub Γ S (open_ct U (cse_loc l)) T.
Proof with eauto*.
  intros * Typ.
  forwards (WfStore & WfCtx & _ & WfT): typing_regular Typ.
  dependent induction Typ.
  - Case "typing_app".
    repeat eexists...
    apply sub_reflexivity...
  - Case "typing_sub".
    rename select (sub Γ S R T) into Sub.
    assert (WfR : wf_typ Γ S R) by applys sub_regular Sub.
    destruct (IHTyp f l ltac:(reflexivity) WfStore WfCtx WfR) as [C [D [Q [U [fTyp [xTyp Sub']]]]]].
    repeat eexists...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_tapp : forall Γ S (l : loc) V T,
  typing Γ S (l @ [V]) T ->
  exists C R U, typing Γ S l (C # (∀ [R] U))
             /\ sub Γ S V R
             /\ sub Γ S (open_tt U V) T.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.
  - Case "typing_tapp".
    exists C, Q, T.
    repeat split...
    apply sub_reflexivity...
    forwards (WfStore & WCtx & _ & WfCQT): typing_regular Typ.
    inversion WfCQT; subst.
    inversion select (wf_typ Γ S (∀ [Q] T)); subst.
    rename select (forall X : atom, X ∉ L -> wf_typ _ _ _) into WfT.
    pick fresh Y and specialize WfT.
    replace (open_tt T V) with (subst_tt Y V (open_tt T Y)) by (rewrite <- subst_tt_intro; eauto).
    rewrite_env (map (subst_tb Y V) nil ++ Γ).
    eapply wf_typ_subst_tb...
    + applys sub_pure_type...
    + apply ok_cons...
  - Case "typing_sub".
    destruct (IHTyp l V eq_refl) as [C [R' [U [fTyp [lTyp Sub]]]]].
    exists C, R', U.
    repeat split...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_box : forall Γ S l T,
  typing Γ S (box l) T ->
  exists C R, typing Γ S l (C # R)
           /\ `cse_fvars` C ⊆ dom Γ
           /\ sub Γ S ({} # □ (C # R)) T.
Proof with eauto*.
  intros * Typ.
  forwards (WfStore & WfCtx & _ & WfT): typing_regular Typ.
  dependent induction Typ...
  - Case "typing_box".
    exists C, R.
    repeat split...
    + intros x InC.
      apply wf_cse_free_vars_bound with (X := x) in H0...
      destruct H0 as [T Binds].
      apply binds_In with (a := bind_typ T)...
    + apply sub_reflexivity...
  - Case "typing_sub".
    rename select (sub Γ S R T) into Sub.
    assert (WfR : wf_typ Γ S R) by applys sub_regular Sub.
    destruct (IHTyp l eq_refl WfStore WfCtx WfR) as [C [R' [lTyp [xSubΓ CRsubS]]]].
    exists C, R'.
    repeat split...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_unbox : forall Γ S C l T,
  typing Γ S (exp_unbox C l) T ->
  exists R, typing Γ S l ({} # (□ (C # R)))
         /\ sub Γ S (C # R) T.
Proof with eauto*.
  intros * Typ.
  forwards (WfStore & WfCtx & _ & WfT): typing_regular Typ.
  dependent induction Typ...
  - Case "typing_unbox".
    exists R.
    repeat split...
    apply sub_reflexivity...
  - Case "typing_sub".
    rename select (sub Γ S R T) into Sub.
    assert (WfR : wf_typ Γ S R) by applys sub_regular Sub.
    destruct (IHTyp _ _ eq_refl WfStore WfCtx WfR) as [R' [xTyp CRsubS]].
    exists R'.
    repeat split...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma preservation : forall Σ Σ' V,
  state_typing Σ V ->
  Σ --> Σ' ->
  state_typing Σ' V.
Proof with eauto*.
  intros * [S E e C1 R1 C2 R2 v StoreTyp EvalTyp Typ] Red.
  forwards (WfStore & WfCtx & WfC1R1 & WfC2R2): eval_typing_regular EvalTyp.
  dependent induction Red.
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
  - Case "red_let_var".
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

Lemma binds_implies_store : forall S Γ x T,
  S ∷ Γ ->
  binds x (bind_typ T) Γ ->
  exists v, stores S x v.
Proof with eauto*.
  intros * StoreTyp Binds.
  induction StoreTyp; binds_cases Binds.
  - Case "x <> x0".
    rename select (binds x _ _) into Binds.
    destruct (IHStoreTyp Binds) as [w Stores].
    exists w.
    apply binds_tail...
  - SCase "x = x0".
    exists v.
    apply binds_head...
Qed.

(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall Γ v C U1 U2,
  no_type_bindings Γ ->
  value v ->
  Γ ⊢ v : (C # (∀ (U1) U2)) ->
  exists S1 e, v = λ (S1) e
             /\ Γ ⊢ U1 <: S1.
Proof with eauto*.
  intros * NTB Val Typ.
  remember (∀ (U1) U2).
  revert U1 U2 Heqt.
  assert (WfEnv : Γ ⊢ wf) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - Case "typing_abs".
    inversion Eq; subst.
    exists (C0 # R), e1.
    repeat split...
    eapply sub_reflexivity...
  - Case "typing_sub".
    destruct (proj2 (sub_capt_type _ _ _ H) ltac:(eauto)) as [D [Q Eq]]; subst.
    inversion select (_ ⊢ _ <: _); subst.
    inversion select (_ ⊢ _ <: (∀ (_) _)); subst.
    + rename select (binds X (bind_sub U) Γ) into Binds.
      contradict Binds; apply (NTB X U).
    + destruct (IHTyp D NTB Val (∀ (C1 # R1) T1) eq_refl WfEnv (C1 # R1) T1 eq_refl) as [S' [e' [Eq Sub]]].
      exists S', e'.
      repeat split...
      apply sub_transitivity with (Q := C1 # R1)...
Qed.

Lemma canonical_form_tabs : forall Γ v C U1 U2,
  no_type_bindings Γ ->
  value v ->
  Γ ⊢ v : (C # ∀ [U1] U2) ->
  exists S1 e, v = Λ [S1] e
            /\ Γ ⊢ U1 <: S1.
Proof with eauto*.
  intros * NTB Val Typ.
  remember (∀ [U1] U2).
  revert U1 U2 Heqt.
  assert (WfEnv : Γ ⊢ wf) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - Case "typing_tabs".
    inversion Eq; subst.
    exists U1, e1.
    repeat split...
    eapply sub_reflexivity...
  - Case "typing_sub".
    destruct (proj2 (sub_capt_type _ _ _ H) ltac:(eauto)) as [D [Q Eq]]; subst.
    inversion select (_ ⊢ _ <: _); subst.
    inversion select (_ ⊢ _ <: (∀ [_] _)); subst.
    + rename select (binds X (bind_sub U) Γ) into Binds.
      contradict Binds; apply (NTB X U).
    + destruct (IHTyp D NTB Val (∀ [R1] T1) eq_refl WfEnv R1 T1 eq_refl) as [S' [e' [Eq Sub]]].
      exists S', e'.
      repeat split...
      apply sub_transitivity with (Q := R1)...
Qed.

Lemma canonical_form_box : forall Γ v D C R,
  no_type_bindings Γ ->
  value v ->
  Γ ⊢ v : (D # (□ C # R)) ->
  exists x, v = box x.
Proof with eauto*.
  intros * NTB Val Typ.
  remember (D # (□ C # R)).
  forwards (WfEnv & _ & Wft): typing_regular Typ.
  assert (Sub : Γ ⊢ t <: (D # (□ C # R))).
  { rewrite <- Heqt.
    apply sub_reflexivity...
  }
  clear Heqt.
  revert R Sub.
  dependent induction Typ; intros R' Sub; subst; try solve [ inversion Val | inversion Sub; inversion select (Γ ⊢ _ <: (□ _)) ].
  - Case "typing_box".
    exists x.
    repeat split...
  - Case "typing_sub".
    assert (Γ ⊢ S <: (D # (□ C # R'))).
    { apply sub_transitivity with (Q := T)... }
    destruct (proj2 (sub_capt_type _ _ _ H0) ltac:(eauto)) as [D' [Q' Eq]]; subst.
    inversion select (Γ ⊢ (D' # Q') <: (D # (□ C # R'))); subst.
    inversion select (Γ ⊢ Q' <: (□ C # R')); subst.
    + rename select (binds X (bind_sub U) Γ) into Binds.
      contradict Binds; apply (NTB X U).
    + assert (WfDBT1 : Γ ⊢ (D' # (□ T1)) wf) by applys sub_regular H0.
      destruct (IHTyp NTB Val WfEnv WfDBT1 R') as [e' Sub']...
Qed.

Lemma progress : forall Σ V, 
  state_typing Σ V ->
  state_final Σ \/ exists Σ', Σ --> Σ'.
Proof with eauto*.
  intros * [S Γ E e C1 R1 C2 R2 StoreTyp EvalTyp Typ].
  assert (NTB : no_type_bindings Γ) by applys store_typing_no_type_bindings StoreTyp.
  eremember (C1 # R1) as T.
  forwards (WfEnv & _ & WfT): typing_regular Typ.
  assert (Γ ⊢ T <: (C1 # R1)).
  { rewrite <- HeqT; apply sub_reflexivity... }
  clear HeqT.
  generalize dependent R1.
  generalize dependent C1.
  dependent induction Typ; intros C' R' Sub.
  - Case "typing_var".
    inversion EvalTyp; subst.
    + left; apply final_state, answer_var.
    + right.
      exists ⟨ S | E0 | open_ve k x (`cset_fvar` x) ⟩.
      destruct (binds_implies_store _ _ _ _ StoreTyp H0) as [v Stores].
      eapply red_let_var...
  - Case "typing_abs".
    assert (Val : value (exp_abs (C # R) e1)).
    { apply value_abs.
      apply expr_abs with (L := L).
      * eapply type_from_wf_typ, H.
      * intros x NotIn.
        rename select (forall x : atom, x ∉ L -> _ ⊢ _ : _) into Typ.
        specialize (Typ x NotIn).
        applys typing_regular Typ.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (λ (C # R) e1))] ++ S | E0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_app".
    right.
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ1) as [Cf [Rf [fBinds [fsubC [WfCf [RfsubDQT PureDQT]]]]]].
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ2) as [Cx [Rx [xBinds [xsubD [WfCx [RxsubQ PureQ]]]]]].
    destruct (binds_implies_store _ _ _ _ StoreTyp fBinds) as [abs absStores].
    destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [arg argStores].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp absStores Typ1) as [Df [Qf [absTyp [fBinds' [absSubCf QfsubDQT]]]]].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp argStores Typ2) as [Dx [Qx [argTyp [xBinds' [argSubCx QxsubQ]]]]].
    apply typing_sub with (T := exp_cv abs # (∀ ((D # Q)) T)) in absTyp.
    2: {
      apply sub_capt...
      - apply subcapt_reflexivity...
      - enough (WfDfQf : Γ ⊢ (Df # Qf) wf) by (inversion WfDfQf; assumption).
        eapply wf_typ_from_binds_typ...
    }
    assert (absValue : value abs) by (eapply stores_implies_value; eauto).
    destruct (canonical_form_abs _ _ _ _ _ NTB absValue absTyp) as [S1 [e [Eq DQsubS1]]].
    rewrite Eq in *.
    assert (absValue' : value (λ (S1) e)).
    { inversion absValue; subst... }
    exists ⟨ S | E | open_ve e x (`cset_fvar` x) ⟩.
    eapply red_app...
  - Case "typing_let".
    right.
    pick fresh z for (dom S).
    assert (k_scope : scope k).
    { econstructor.
      intros x NotIn.
      rename select (forall x : atom, x ∉ L -> _ ⊢ _ : _) into Typ'.
      specialize (Typ' x NotIn).
      applys typing_regular Typ'.
    }
    exists ⟨ S | k :: E | e ⟩.
    apply red_let_exp, k_scope.
  - Case "typing_tabs".
    assert (Val : value (exp_tabs V0 e1)).
    { apply value_tabs.
      apply expr_tabs with (L := L)...
      intros x NotIn.
      rename select (forall X : atom, X ∉ L -> _ ⊢ _ : _) into Typ.
      specialize (Typ x NotIn).
      applys typing_regular Typ.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (Λ [V0] e1))] ++ S | E0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_tapp".
    right.
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ) as [Cx [Rx [xBinds [xsubC [WfCx [RxsubQT PureQT]]]]]].
    destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [tabs tabsStores].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp tabsStores Typ) as [Dx [Qx [tabsTyp [fBinds' [tabsSubCx QfsubQT]]]]].
    apply typing_sub with (T := exp_cv tabs # (∀ [Q] T)) in tabsTyp.
    2: {
      apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QfsubQT...
    }
    assert (tabsValue : value tabs) by (eapply stores_implies_value; eauto).
    destruct (canonical_form_tabs _ _ _ _ _ NTB tabsValue tabsTyp) as [S1 [e [Eq DQsubS1]]].
    rewrite Eq in *.
    assert (tabsValue' : value (Λ [S1] e)).
    { inversion tabsValue; subst... }
    exists ⟨ S | E | open_te e P ⟩.
    eapply red_tapp...
    assert (PureQ : pure_type Q) by (inversion PureQT; assumption).
    applys sub_pure_type H...
  - Case "typing_box".
    assert (Val : value (box x)).
    { apply value_box... }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (box x))] ++ S | E0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_unbox".
    right.
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ) as [Cx [Rx [xBinds [xsubC [WfCx [RxsubQT PureQT]]]]]].
    destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [box' boxStores].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp boxStores Typ) as [Dx [Qx [boxTyp [xBinds' [boxSubCx QxsubQT]]]]].
    apply typing_sub with (T := exp_cv box' # (□ C # R)) in boxTyp.
    2: {
      apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QxsubQT...
    }
    assert (boxValue : value box') by (eapply stores_implies_value; eauto).
    destruct (canonical_form_box _ _ _ _ _ NTB boxValue boxTyp) as [y Eq].
    rewrite Eq in *.
    assert (boxValue' : value (box y)).
    { inversion boxValue; subst... }
    exists ⟨ S | E | y ⟩.
    eapply red_open...
  - Case "typing_sub".
    eapply IHTyp...
    + eapply eval_typing_sub with (S1 := T) (T1 := C2 # R2)...
      eapply sub_reflexivity...
      applys eval_typing_regular EvalTyp.
    + apply sub_transitivity with (Q := T)...
Qed.
