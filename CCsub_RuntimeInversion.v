Require Import Coq.Program.Equality.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.
Require Import CCsub_Red.

Hint Constructors store_typing eval_typing state_typing : core.

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

Lemma typed_store_ctx_wf : forall S SS,
  store_typing SS S ->
  wf_store_ctx S.
Proof with eauto.
  intros. dependent induction H...
  constructor...
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
    - destruct H4 as [C' [R' Binds]].
      rewrite_env ([(l0, (C # R))] ++ S) in Binds.
      Store.binds_cases Binds; subst.
      + assert (exists C R, Store.binds l (C # R) S) by (exists C', R'; eauto).
        destruct (IHStoreTyp H5) as [v0 [E0 Stores]].
        exists v0, E0.
        apply Store.binds_tail with (F := [(l0, store (v, E))]) in Stores; simpl in *...
      + inversion H6; subst.
        exists v, E.
        rewrite_env ([(l, store (v, E))] ++ SS).
        apply Store.binds_head, Store.binds_singleton.
   }
  {
    dependent induction StoreTyp.
    - destruct H as [v [E Binds]]. inversion Binds.
    - destruct H4 as [v0 [E0 Binds]].
      rewrite_env ([(l0, store (v, E))] ++ SS) in Binds.
      unfold stores in Binds. Store.binds_cases Binds; subst.
      + assert (exists v E, stores l (v, E) SS) by (exists v0, E0; eauto).
        destruct (IHStoreTyp H5) as [C' [R' Stores]].
        exists C', R'.
        apply Store.binds_tail with (F := [(l0, (C # R))]) in Stores; simpl in *...
      + inversion H6; subst.
        exists C, R.
        rewrite_env ([(l, (C # R))] ++ S).
        apply Store.binds_head, Store.binds_singleton.
  }
Qed.

Lemma store_typing_inversion : forall S SS E l v U,
  store_typing SS S ->
  Store.binds l U S ->
  stores l (v, E) SS ->
  exists Γ, (typing Γ S v U /\ env_well_typed S E Γ /\ wf_typ nil S U /\ value(v, E)).
Proof with eauto using typing_weakening_store, env_well_typed_weaken_store, wf_typ_weakening_store.
  intros * StoreTyp lBindsU lBindsv.
  dependent induction StoreTyp.
  inversion lBindsU.
  assert (WfStore : wf_store_ctx S) by applys typed_store_ctx_wf StoreTyp.
  rewrite_env ([(l0, (C # R))] ++ S) in lBindsU.
  Store.binds_cases lBindsU; subst.
  - rewrite_env ([(l0, store (v0, E0))] ++ SS) in lBindsv.
    unfold stores in lBindsv. Store.binds_cases lBindsv...
    + destruct (IHStoreTyp H4 H5) as [Γ0 [Typ [EnvTyp [WfU Val]]]].
      assert (wf_store_ctx ([(l0, C # R)] ++ S)) by (constructor; eauto).
      exists Γ0; rewrite_env (nil ++ [(l0, C # R)] ++ S)...
      repeat split...
    + simpl in Fr; flsetdec.
  - rewrite_env ([(l, store (v0, E0))] ++ SS) in lBindsv.
    unfold stores in lBindsv. Store.binds_cases lBindsv...
    + simpl in Fr; flsetdec.
    + inversion H6; subst.
      assert (wf_store_ctx ([(l, C # R)] ++ S)) by (constructor; eauto).
      exists Γ; rewrite_env (nil ++ [(l, C # R)] ++ S).
      repeat split; auto.
      apply typing_weakening_store...
      apply env_well_typed_weaken_store...
      apply wf_typ_weakening_store...
Qed.

Lemma env_typing_equivalent : forall S E Γ x,
  env_well_typed S E Γ ->
  (exists l T, binds x (T, l) E) <-> (exists C R, binds x (bind_typ (C # R)) Γ).
Proof with eauto.
  intros * EnvTyp. dependent induction EnvTyp; split; intros.
  1,2: destruct H0 as [? [? Binds]]; inversion Binds.
  - destruct H2 as [l0 [T Binds]].
    binds_cases Binds; subst.
    + assert (exists l T, binds x (T, l) E) by (exists l0, T; eauto).
      destruct ((proj1 IHEnvTyp) H3) as [C0 [R0 Binds]].
      exists C0, R0.
      apply binds_tail with (F := [(x0, bind_typ (C # R))]) in Binds; simpl in *...
    + inversion H4; subst.
      exists C, R.
      apply binds_head, binds_singleton.
  - destruct H2 as [C0 [R0 Binds]].
    binds_cases Binds; subst.
    + assert (exists C R, binds x (bind_typ (C # R)) Γ) by (exists C0, R0; eauto).
      destruct ((proj2 IHEnvTyp) H3) as [l0 [T Binds]].
      exists l0, T.
      apply binds_tail with (F := [(x0, (C # R, l))]) in Binds; simpl in *...
    + inversion H4; subst.
      exists l, (C # R).
      apply binds_head, binds_singleton.
Qed.

Lemma env_typing_inversion : forall S E Γ x C R l,
  env_well_typed S E Γ ->
  binds x (C # R, l) E ->
  Store.binds l (C # R) S /\ binds x (bind_typ (C # R)) Γ /\ wf_typ Γ S (C # R).
Proof with eauto.
  intros * EnvTyp Binds.
  dependent induction EnvTyp.
  { inversion Binds. }
  assert (WfCtx : wf_ctx Γ S) by (eapply env_well_typed_ctx_wf; eauto).
  binds_cases Binds; subst.
  - destruct (IHEnvTyp H2) as [StoreBinds [Binds Wf]].
    repeat split...
    rewrite_nil_concat.
    eapply wf_typ_weakening...
    constructor...
  - inversion H4; subst.
    repeat split...
    rewrite_nil_concat.
    eapply wf_typ_weakening...
    constructor...
Qed.

(* Lemma stores_preserves_typing : forall SS Γ S E E' (x : atom) l v C R T, *)
(*   store_typing SS S -> *)
(*   env_well_typed S E Γ -> *)
(*   binds x (T, l) E -> *)
(*   stores l (v, E') SS -> *)
(*   typing Γ S x (C # R) -> *)
(*   exists D Q, typing Γ S v (exp_cv v # Q) *)
(*          /\ binds x (bind_typ (D # Q)) Γ *)
(*          /\ subcapt Γ S (exp_cv v) D *)
(*          /\ sub Γ S Q R. *)
(* Proof with eauto. *)
(*   intros * StoreTyp EnvTyp Binds Stores. *)
(*   revert C R. *)
(*   dependent induction StoreTyp. *)
(*   { inversion Stores. } *)
(*   intros C0 R0 xTyp. *)
