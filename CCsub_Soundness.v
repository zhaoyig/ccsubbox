Require Import Coq.Program.Equality.
Require Import Lia.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.
Require Import LibTactics.

Set Nested Proofs Allowed.

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

Inductive env_well_typed : ctx -> store_ctx -> env -> Prop :=
  | ee_empty : forall S,
      (* wf_ctx Γ -> *)
      wf_store_ctx S ->
      env_well_typed nil S nil
  | ee_cons : forall Γ Γ' S E x l C R,
      env_well_typed Γ S E ->
      (* binds x (bind_typ T) Γ -> *)
      x `notin` dom Γ ->
      (* wf_typ Γ T -> *)
      Store.binds l (C # R, Γ') S ->
      (* sub Γ U T -> *)
      env_well_typed ((x, bind_typ (C # R)) :: Γ) S ((x, l)::E).

Inductive store_typing : store_env -> store_ctx  -> Prop :=
  | typing_store_nil:
      store_typing nil nil
  | typing_store_cons : forall l C R v Γ SS E S,
      store_typing SS S ->
      value (v, E) ->
      typing Γ v (C # R) ->
      env_well_typed Γ S E ->
      l `Notin` Store.dom S ->
      store_typing ((l, store (v , E)) :: SS) ((l, (C # R, Γ)) :: S).

Inductive eval_typing (S : store_ctx) : cont -> typ -> typ -> Prop :=
  | typing_eval_nil : forall Γ C1 R1 C2 R2,
      sub Γ (C1 # R1) (C2 # R2) ->
      eval_typing S nil (C1 # R1) (C2 # R2)
  | typing_eval_cons : forall Γ L e K C1 R1 C2 R2 C3 R3 E,
      scope e ->
      (forall x, x ∉ L ->
        typing ([(x, bind_typ (C1 # R1))] ++ Γ) (open_ve e x (cse_fvar x)) (C2 # R2)) ->
      env_well_typed Γ S E ->
      eval_typing S K (C2 # R2) (C3 # R3) ->
      eval_typing S ((let_body (e, E)) :: K) (C1 # R1) (C3 # R3).

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall Γ S E SS K C1 R1 C2 R2 e,
      store_typing SS S ->
      eval_typing S K (C1 # R1) (C2 # R2) ->
      typing Γ e (C1 # R1) ->
      env_well_typed Γ S E ->
      state_typing ⟨ (e, E) | SS | K ⟩ (C2 # R2).

Inductive red : state -> state -> Prop :=
  | red_var : forall (x : atom) l SS K E eE,
      binds x l E ->
      stores l eE SS ->
      red ⟨ (exp_var x, E) | SS | K ⟩
          ⟨ eE | SS | K ⟩
  | red_app : forall (x y z: atom) T e1 lx ly v E SS K E',
      binds x lx E ->
      binds y ly E ->
      stores lx (λ (T) e1,  E') SS ->
      stores ly v SS ->
      z `notin` dom E' ->
      red ⟨ (exp_app x y, E) | SS | K ⟩
          ⟨ (open_ve e1 z (cse_fvar z), (z, ly) :: E') | SS | K ⟩
  | red_tapp : forall (x : atom) T l R e1 E E' SS K,
      binds x l E ->
      stores l (Λ [R] e1, E') SS ->
      red ⟨ (x @ [T], E) | SS | K ⟩
          ⟨ (open_te e1 T, E') | SS | K ⟩
  | red_let : forall b e E SS K,
      red ⟨ (let= b in e, E) | SS | K ⟩
          ⟨ (b, E) | SS | (let_body (e, E)) :: K ⟩
  | red_let_val : forall (z: atom) E K e v SS l,
      z `notin` dom E ->
      l `Notin` Store.dom SS ->
      value v ->
      red ⟨ v | SS | (let_body (e, E)) :: K ⟩
          ⟨ (open_ve e z (cse_fvar z), (z, l) :: E) | (l, store v) :: SS | K ⟩
  | red_open : forall (x : atom) l x y C E E' SS K,
      binds x l E ->
      stores l (box y, E') SS ->
      red ⟨ (C ⟜ x, E) | SS | K ⟩
          ⟨ ((exp_var y), E) | SS | K ⟩.

Hint Constructors store_typing eval_typing state_typing : core.

(*
Lemma eval_typing_regular : forall S K T U,
  eval_typing S K T U ->
  exists Γ,
    wf_ctx Γ /\ wf_typ Γ T /\ wf_typ Γ U.
Proof with eauto*.
  intros * EvalTyp.
  induction EvalTyp.
  - rename select (sub _ _ _) into Sub.
    apply sub_regular in Sub as [WfE [WfT' WfT]].
    repeat split...
  - pick fresh x and specialize H.
    destructs typing_regular H as [wf_xTE _].
    inversion wf_xTE; subst.
Qed.
 *)

Lemma env_implies_value : forall S E l v,
  store_typing E S ->
  stores l v E ->
  value v.
Proof with eauto*.
  intros * StoreTyp Stores.
  induction StoreTyp; inversion Stores; subst.
  destruct (l ==== l0); subst...
Qed.

(*
Lemma stores_preserves_typing : forall S E l v C P,
  store_typing E S ->
  stores l v E ->
  typing nil l (C # P) ->
  exists D Q, typing nil v (exp_cv v # Q)
         /\ Store.binds l (D # Q) S
         /\ subcapt nil (exp_cv v) D
         /\ sub nil Q P.
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
  sub Γ R2 R1 ->
  eval_typing S K R1 T1 ->
  sub Γ T1 T2 ->
  eval_typing S K R2 T2.
Proof with eauto*.
  intros * R2SubR1 EvalTyp T1SubT2.
  revert R2 T2 R2SubR1 T1SubT2.
  induction EvalTyp; intros R4 T2 R2subC1R1 C2R2subT2.
  - Case "typing_eval_nil".
    rename select (sub Γ0 (C1 # R1) (C2 # R2)) into C1R1subC2R2.
    destruct (proj1 (sub_capt_type _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst.
    destruct (proj2 (sub_capt_type _ _ _ R2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst.
    apply typing_eval_nil...
    apply sub_transitivity with (Q := C1 # R1)...
    apply sub_transitivity with (Q := C2 # R2)...
  - Case "typing_eval_cons".
    destruct (proj1 (sub_capt_type _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst.
    destruct (proj2 (sub_capt_type _ _ _ R2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst.
    apply typing_eval_cons with (L := L) (C2 := C2) (R2 := R2)...
    + intros x xNotIn.
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
    + apply IHEvalTyp...
      apply sub_reflexivity...
      applys eval_typing_regular EvalTyp.
Qed.
 *)

(* Lemma eval_typing_weakening : forall Γ Δ Θ S K T U, *)
(*   eval_typing (Δ ++ Γ) S K T U -> *)
(*   wf_ctx (Δ ++ Θ ++ Γ) -> *)
(*   eval_typing (Δ ++ Θ ++ Γ) S K T U. *)
(* Proof with eauto*. *)
(*   intros * EvalTyp WfCtx. *)
(*   induction EvalTyp. *)
(*   - Case "typing_eval_nil". *)
(*     apply typing_eval_nil... *)
(*     apply sub_weakening... *)
(*   - Case "typing_eval_cons". *)
(*     apply typing_eval_cons with (L := L `u`A dom (Δ ++ Θ ++ Γ)) (C2 := C2) (R2 := R2)... *)
(*     intros x xNotIn. *)
(*     rename select (forall x, x ∉ L -> typing _ _ _) into Typ. *)
(*     specialize (Typ x ltac:(fsetdec)). *)
(*     rewrite <- concat_assoc in Typ. *)
(*     apply typing_weakening with (Θ := Θ) in Typ. *)
(*     + apply Typ. *)
(*     + simpl_env. *)
(*       apply wf_ctx_typ... *)
(*       assert (WfCtx' : wf_ctx (([(x, bind_typ (C1 # R1))] ++ Δ) ++ Γ)) by applys typing_regular Typ. *)
(*       inversion WfCtx'; subst. *)
(*       apply wf_typ_weakening... *)
(*     + inversion H0; subst; try econstructor... *)
(*       eapply ee_cons... *)
(*       apply wf_typ_weakening... *)
(* Qed. *)

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

Lemma typing_inv_app : forall Γ (f x : atom) T,
  typing Γ (f @ x) T ->
  exists C D Q U, typing Γ f (C # (∀ (D # Q) U))
               /\ typing Γ x (D # Q)
               /\ sub Γ (open_ct U (cse_fvar x)) T.
Proof with eauto*.
  intros * Typ.
  forwards (WfCtx & _ & WfT): typing_regular Typ.
  dependent induction Typ.
  - Case "typing_app".
    repeat eexists...
    apply sub_reflexivity...
  - Case "typing_sub".
    rename select (sub Γ R T) into Sub.
    assert (WfR : wf_typ Γ R) by applys sub_regular Sub.
    destruct (IHTyp f x ltac:(reflexivity) WfCtx WfR) as [C [D [Q [U [fTyp [xTyp Sub']]]]]].
    repeat eexists...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_tapp : forall Γ (x : atom) V T,
  typing Γ (x @ [V]) T ->
  exists C R U, typing Γ x (C # (∀ [R] U))
             /\ sub Γ V R
             /\ sub Γ (open_tt U V) T.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.
  - Case "typing_tapp".
    exists C, Q, T.
    repeat split...
    apply sub_reflexivity...
    forwards (WCtx & _ & WfCQT): typing_regular Typ.
    inversion WfCQT; subst.
    inversion select (wf_typ Γ (∀ [Q] T)); subst.
    rename select (forall X : atom, X ∉ L -> wf_typ _ _) into WfT.
    pick fresh Y and specialize WfT.
    replace (open_tt T V) with (subst_tt Y V (open_tt T Y)) by (rewrite <- subst_tt_intro; eauto).
    rewrite_env (map (subst_tb Y V) nil ++ Γ).
    eapply wf_typ_subst_tb...
    + applys sub_pure_type...
    + apply ok_cons...
  - Case "typing_sub".
    destruct (IHTyp x V eq_refl) as [C [R' [U [fTyp [lTyp Sub]]]]].
    exists C, R', U.
    repeat split...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_box : forall Γ x T,
  typing Γ (box x) T ->
  exists C R, typing Γ x (C # R)
           /\ `cse_fvars` C ⊆ dom Γ
           /\ sub Γ ({} # □ (C # R)) T.
Proof with eauto*.
  intros * Typ.
  forwards (WfCtx & _ & WfT): typing_regular Typ.
  dependent induction Typ...
  - Case "typing_box".
    exists C, R.
    repeat split...
    + intros x InC.
      apply wf_cse_free_vars_bound with (X := x) in H...
      destruct H as [T Binds].
      apply binds_In with (a := bind_typ T)...
    + apply sub_reflexivity...
  - Case "typing_sub".
    rename select (sub Γ R T) into Sub.
    assert (WfR : wf_typ Γ R) by applys sub_regular Sub.
    destruct (IHTyp x eq_refl WfCtx WfR) as [C [R' [lTyp [xSubΓ CRsubS]]]].
    exists C, R'.
    repeat split...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_unbox : forall Γ C x T,
  typing Γ (exp_unbox C x) T ->
  exists R, typing Γ x ({} # (□ (C # R)))
         /\ sub Γ (C # R) T.
Proof with eauto*.
  intros * Typ.
  forwards (WfCtx & _ & WfT): typing_regular Typ.
  dependent induction Typ...
  - Case "typing_unbox".
    exists R.
    repeat split...
    apply sub_reflexivity...
  - Case "typing_sub".
    rename select (sub Γ R T) into Sub.
    assert (WfR : wf_typ Γ R) by applys sub_regular Sub.
    destruct (IHTyp _ _ eq_refl WfCtx WfR) as [R' [xTyp CRsubS]].
    exists R'.
    repeat split...
    apply sub_transitivity with (Q := R)...
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

Lemma typed_store_ok : forall SS S,
  store_typing SS S ->
  Store.ok SS.
Proof with eauto.
  intros. dependent induction H...
  constructor...
  rewrite store_typing_preserves_dom with (S := S)...
Qed.

Lemma env_well_typed_store_ctx_wf : forall Γ S E,
  env_well_typed Γ S E ->
  wf_store_ctx S.
Proof with eauto.
  intros. dependent induction H...
Qed.

Lemma env_well_typed_ctx_wf : forall Γ S E,
  env_well_typed Γ S E ->
  wf_ctx Γ.
Proof with eauto.
  intros. dependent induction H...
  rewrite_env ([(x, bind_typ (C # R))] ++ Γ).
  constructor...
  apply env_well_typed_store_ctx_wf in H.
  Admitted.
(*   inversion H... *)
(* Qed. *)

Hint Resolve typed_store_ctx_wf : core.

Lemma env_well_typed_weaken_store : forall Γ S1 S2 S3 E,
  env_well_typed Γ (S1 ++ S3) E ->
  wf_store_ctx (S1 ++ S2 ++ S3) ->
  env_well_typed Γ (S1 ++ S2 ++ S3) E.
Proof with eauto.
  intros * EnvTyp WfStore.
  dependent induction EnvTyp.
  - constructor...
  - econstructor...
    apply wf_store_ctx_ok in WfStore.
    Store.binds_cases H0...
Qed.

Lemma store_typing_equivalent : forall S SS l,
  store_typing SS S ->
  (exists U Γ, Store.binds l (U, Γ) S) <-> (exists v E, stores l (v, E) SS).
Proof with eauto.
  intros * StoreTyp.
  split; intros.
  {
    dependent induction StoreTyp.
    - destruct H as [U [Γ Binds]].
      inversion Binds.
    - destruct H3 as [U [Γ' Binds]].
      rewrite_env ([(l0, (C # R, Γ))] ++ S) in Binds.
      apply Store.binds_concat_inv in Binds.
      destruct Binds; simpl in *...
      + destruct H3.
        assert (exists (U : typ) (Γ : ctx), Store.binds l (U, Γ) S). {
          exists U, Γ'...
        }
        destruct (IHStoreTyp H5) as [v0 [E0 Stores]].
        exists v0, E0.
        apply Store.binds_tail with (F := [(l0, store (v, E))]) in Stores.
        simpl in Stores...
        simpl; flsetdec.
      + apply Store.binds_singleton_inv in H3.
        destruct H3; inversion H4; subst.
        exists v, E.
        rewrite_env ([(l0, store (v, E))] ++ SS).
        apply Store.binds_head, Store.binds_singleton.
   }
  {
    dependent induction StoreTyp.
    - destruct H as [U [Γ Binds]].
      inversion Binds.
    - destruct H3 as [v0 [E0 Binds]].
      rewrite_env ([(l0, store (v, E))] ++ SS) in Binds.
      apply Store.binds_concat_inv in Binds.
      destruct Binds; simpl in *...
      + destruct H3.
        assert (exists v E, stores l (v, E) SS) by (exists v0, E0; eauto).
        destruct (IHStoreTyp H5) as [U [Γ' Stores]].
        exists U, Γ'.
        apply Store.binds_tail with (F := [(l0, (C # R, Γ))]) in Stores.
        simpl in Stores...
        simpl; flsetdec.
      + apply Store.binds_singleton_inv in H3.
        destruct H3; inversion H4; subst.
        exists (C # R), Γ.
        rewrite_env ([(l0, (C # R, Γ))] ++ S).
        apply Store.binds_head, Store.binds_singleton.
  }
Qed.

Lemma store_typing_inversion : forall Γ S SS E l v U,
  store_typing SS S ->
  Store.binds l (U, Γ) S ->
  stores l (v, E) SS ->
  typing Γ v U /\ env_well_typed Γ S E.
Proof with eauto.
  intros * StoreTyp lBindsU lBindsv.
  dependent induction StoreTyp.
  inversion lBindsU.
  assert (WfStore : wf_store_ctx S) by applys typed_store_ctx_wf StoreTyp.
  rewrite_env ([(l0, (C # R, Γ0))] ++ S) in lBindsU.
  apply Store.binds_concat_inv in lBindsU.
  destruct lBindsU; simpl in *...
  - destruct H3.
    rewrite_env ([(l0, store (v0, E0))] ++ SS) in lBindsv.
    apply Store.binds_concat_inv in lBindsv.
    destruct lBindsv.
    + destruct H5...
      destruct (IHStoreTyp H4 H6); split...
      rewrite_env (nil ++ [(l0, (C # R, Γ0))] ++ S).
      eapply env_well_typed_weaken_store...
      constructor...
    + apply Store.binds_singleton_inv in H5...
      destruct H5; clear - H3 H5; flsetdec.
  - apply Store.binds_singleton_inv in H3...
    destruct H3; subst.
    rewrite_env ([(l0, store (v0, E0))] ++ SS) in lBindsv.
    apply Store.binds_concat_inv in lBindsv.
    destruct lBindsv.
    + clear - H3; destruct H3; simpl in *; flsetdec.
    + apply Store.binds_singleton_inv in H3...
      destruct H3.
      inversion H4; inversion H5; subst...
      split...
      rewrite_env (nil ++ [(l0, (C # R, Γ0))] ++ S).
      eapply env_well_typed_weaken_store...
      constructor...
Qed.

(* Lemma typing_invariant_under_typed_ctx : forall Γ Γ' S E (x : atom) C R, *)
(*   x `in` dom E -> *)
(*   env_well_typed Γ S E -> *)
(*   typing Γ x (C # R) -> *)
(*   env_well_typed Γ' S E -> *)
(*   typing Γ' x (C # R). *)
(* Proof with eauto. *)
(*   intros. generalize dependent Γ. *)
(*   dependent induction H2; intros... *)
(*   simpl in H; fsetdec. *)
(**)
(*   simpl in H. destruct (x == x0); subst... *)
(*   - inversion H4; subst. *)
(*     pose proof (env_well_typed_store_ctx_wf _ _ _ H2). *)
(*     apply wf_store_ctx_ok in H6. *)
(*     pose proof (Store.binds_unique _ _ _ _ _ H6 H1 H13). *)
(*     inversion H7; subst... *)
(*     admit. *)
(*   - assert (x `in` dom E) by fsetdec. *)
(*     inversion H4; subst... *)

Lemma store_type_same_as_ctx : forall Γ Γ' S E x l T1 T2,
  binds x l E ->
  Store.binds l (T1, Γ') S ->
  binds x (bind_typ T2) Γ ->
  env_well_typed Γ S E ->
  T1 = T2.
Proof with eauto.
  intros * BindsxE BindslS BindsxΓ EnvTyp.
  dependent induction EnvTyp.
  inversion BindsxE.
  simpl in *.
  rewrite_env ([(x0, l0)] ++ E) in BindsxE.
  binds_cases BindsxE; subst.
  - apply IHEnvTyp... admit.
  - pose proof (env_well_typed_store_ctx_wf _ _ _ EnvTyp).
    pose proof (env_well_typed_ctx_wf _ _ _ EnvTyp).
    apply wf_store_ctx_ok in H1.
    apply ok_from_wf_ctx in H2.
    (* pose proof (binds_unique _ _ _ _ BindsxΓ H). *)
    (* pose proof (Store.binds_unique _ _ _ _ _ H1 BindslS H0). *)
    (* inversion H3; inversion H4; subst... *)
    Admitted.
(* Qed. *)

Lemma typing_inv_var : forall Γ (x : atom) T,
  typing Γ x T ->
  exists C R, binds x (bind_typ (C # R)) Γ
           /\ sub Γ (C # R) T.
Proof.
Admitted.

Lemma preservation : forall Σ Σ' V,
  state_typing Σ V ->
  red Σ Σ' ->
  state_typing Σ' V.
Proof with eauto*.
  intros * [Γ S E SS K C1 R1 C2 R2 e StoreTyp EvalTyp Typing EnvTyp] Red.
  (* forwards (WfCtx & WfC1R1 & WfC2R2): eval_typing_regular EvalTyp. *)
  dependent induction Red.
  - Case "red_var".
    destruct eE as [e E0].
    (* inversion StoreTyp; subst. inversion H0. *)
    pose proof (proj2 (store_typing_equivalent _ _ l StoreTyp)).
    assert (exists (v : exp) (E : env), stores l (v, E) SS)
      by (exists e, E0; eauto).
    destruct (H1 H2) as [U0 [Γ0 Binds]].
    pose proof (store_typing_inversion _ _ _ _ _ _ _ StoreTyp Binds H0).
    destruct (typing_inv_var _ _ _ Typing) as [C [R [Binds' Sub]]].
    (* destruct H99 as [D [Q [Binds' [Subcapt [_ [Sub _]]]]]]. *)
    eapply typing_state...
    unshelve epose proof (store_type_same_as_ctx Γ Γ0 S E x l U0 (C # R) _ _ _ _); subst...
    destruct H3; eapply typing_sub...
    admit.

    (* admit. *)
  - Case "red_app".
    destruct v as [e E0].
    destruct (proj2 (store_typing_equivalent _ _ lx StoreTyp)) as [U [Γ0 Stores]].
    exists (λ (T) e1), E'...
    destruct (store_typing_inversion _ _ _ _ _ _ _ StoreTyp Stores H1).
    eapply typing_state...
    epose proof (typing_inv_abs _ _ _ _ H4 _ _ _ _).
    destruct H6 as [_ [S2 [L ?]]].




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
  - Case "red_loc".
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
