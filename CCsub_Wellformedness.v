Require Import Coq.Program.Equality.

Require Export CCsub_Infrastructure.
Require Import Meta.MetatheoryAtom.
Require Import Meta.Metatheory.

(* ********************************************************************** *)
(** * #<a name="utils"></a># Automation Utils -- mostly related to wellformedness of environments [ok], [wf_ctx], [dom], ...*)


Lemma cset_from_wf_cse : forall Γ S C,
  wf_cse Γ S C -> cset C.
Proof with auto.
  intros.
  induction H; constructor...
Qed.

Lemma cset_from_wf_cse_in : forall Γ S C, wf_cse Γ S C -> cset C.
Proof. eauto using cset_from_wf_cse. Qed.

Hint Resolve cset_from_wf_cse_in : core.

Lemma allbound_over_union : forall Γ T1 T2,
  allbound Γ (T1 `union`A T2) ->
  allbound Γ T1 /\ allbound Γ T2.
Proof with eauto.
  intros.
  split; intros ? ?; assert (x `in`A (T1 `union`A T2)) by fsetdec...
Qed.

Lemma ok_from_wf_ctx : forall Γ S,
  wf_ctx Γ S ->
  EnvImpl.ok Γ.
Proof.
  intros Γ S H.
  induction H.
  - apply EnvImpl.ok_nil.
  - simpl. apply EnvImpl.ok_cons. auto. auto.
  - simpl. apply EnvImpl.ok_cons. auto. auto.
Qed.

Lemma uniq_from_wf_ctx : forall Γ S,
  wf_ctx Γ S ->
  uniq Γ.
Proof with eauto.
  intros Γ S H.
  induction H...
Qed.

(** We add [ok_from_wf_ctx] as a hint here since it helps blur the
    distinction between [wf_ctx] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_ctx].  Thus,
    [ok_from_wf_ctx] serves as a bridge that allows us to use the
    ctxironments library. *)

Hint Resolve ok_from_wf_ctx uniq_from_wf_ctx : core.

(* This lemma is needed by a couple of lemmas about wf_typ *)
Lemma wf_ctx_tail : forall Γ Δ S,
  wf_ctx (Δ ++ Γ) S ->
  wf_ctx Γ S.
Proof with eauto.
  intros * Hwf.
  induction Δ; (trivial || inversion Hwf; subst)...
Qed.

Hint Resolve wf_ctx_tail : core.

Hint Extern 1 (ok (map ?f ?Δ ++ ?Γ)) =>
match goal with
| H : wf_ctx (Δ ++ ?b ++ Γ) S |- _ =>
  enough (ok (Δ ++ b ++ Γ))
end : core.

Lemma binding_uniq_from_wf_ctx : forall F E S x b,
  wf_ctx (F ++ ([(x, b)]) ++ E) S ->
  x `notin`A (EnvImpl.dom F `union`A EnvImpl.dom E).
Admitted.
(* Proof.
  intros.
  apply ok_from_wf_ctx in H.
  eapply H; eauto.
Qed. *)

(* ********************************************************************** *)
(** * #<a name="wfset"></a># Properties of [wf_cset] *)

Lemma empty_cse_wf : forall Γ S, wf_cse Γ S {}.
Proof.
  intros.
  constructor.
Qed.

Lemma univ_cse_wf : forall Γ S, wf_cse Γ S {*}.
Proof.
  intros.
  constructor.
Qed.

Hint Resolve empty_cse_wf univ_cse_wf : core.

Lemma wf_cse_union : forall Γ S C D,
  wf_cse Γ S C ->
  wf_cse Γ S D ->
  wf_cse Γ S (C `u` D).
Proof with eauto.
  intros *.
  intros H1 H2.
  inversion H1; inversion H2; subst; simpl...
Qed.

Lemma wf_cse_over_join : forall Γ S C D,
  wf_cse Γ S (C `u` D) <->
  wf_cse Γ S C /\ wf_cse Γ S D.
Proof with eauto.
  intros; split; intros H; destruct C eqn:HC1;
                           destruct D eqn:HC2;
                           unfold cse_union in *;
                           inversion H...
Qed.

Hint Resolve wf_cse_union : core.

(** This is a useful helper tactic for clearing away
    capture set wellformedness. *)

(* Ltac wf_cse_simpl instantiate_ext :=
  match goal with
  | H : _ |- (wf_cse _ _ {*}) =>
    constructor
  | H : (wf_cse _ _ ?C) |- (wf_cse _ _ ?C) =>
    let x  := fresh "x" in
    let Hx := fresh "In" x in
    let Hexists := fresh "Hexists" in
    let T := fresh "T" in
    let Hbound := fresh "Hbound" in
    inversion H;
    rename select (allbound _ _) into Hbound;
    subst; constructor;
    intros x Hx;
    destruct (Hbound x Hx) as [C [R Hexists]];
    lazymatch instantiate_ext with
    | True => exists T; destruct Hexists; auto
    | False => idtac
    end
  end. *)

Lemma wf_cse_fvars_from_ctx : forall Γ S C x,
  wf_cse Γ S C ->
  x `in`A (cse_fvars C) ->
  x `in`A EnvImpl.dom Γ.
Proof with eauto.
  intros * Hwf.
  induction Hwf; simpl in *; try fsetdec...
  apply EnvImpl.binds_In in H...
  fsetdec.
Qed.

Lemma wf_cse_weakening : forall F E G S C,
  wf_cse (G ++ E) S C ->
  EnvImpl.ok (G ++ F ++ E) ->
  wf_cse (G ++ F ++ E) S C.
Proof with auto*.
  intros * Hwf Hok.
  remember (G ++ E).
  generalize dependent G.
  induction Hwf; intros G EQ Hok; subst; simpl in *...
  apply (wf_cse_term_fvar T S (G ++ F ++ E) x).
  apply EnvImpl.binds_weaken...
  apply wf_cse_term_loc with (T := T)...
Qed.

Lemma wf_cse_weaken_head : forall C Γ Δ S,
  wf_cse Γ S C ->
  EnvImpl.ok (Δ ++ Γ) ->
  wf_cse (Δ ++ Γ) S C.
Proof.
  intros.
  rewrite_env (nil ++ Δ ++ Γ).
  apply wf_cse_weakening; auto.
Qed.

Ltac destruct_bound H :=
  destruct H as [H|H].

(* Type bindings don't matter at all! *)
Lemma wf_cse_narrowing : forall V U C Γ Δ S X,
  wf_cse (Δ ++ [(X, bind_sub V)] ++ Γ) S C ->
  EnvImpl.ok (Δ ++ [(X, bind_sub U)] ++ Γ) ->
  wf_cse (Δ ++ [(X, bind_sub U)] ++ Γ) S C.
Admitted.
(* Proof with simpl_env; eauto.
  intros *.
  intros Hwf Hok.
  dependent induction Hwf...
  apply (wf_cse_term_fvar T S (Δ ++ [(X, bind_sub U)] ++ Γ) x).
  destruct (x == X).
  - subst. simpl in H.
    EnvImpl.binds_cases H.
    -- unfold binds in Hok. simpl in Hok.
       destruct (X == X)...
       discriminate Hok.
    -- apply EnvImpl.binds_app_2. (* binds_head, formerly *)
  - EnvImpl.EnvImpl.destruct_binds_hyp H.
    -- apply binds_tail...
    -- apply binds_head...  
Qed. *)

Lemma wf_cse_narrowing_typ : forall C1 R1 C2 R2 C Γ Δ X S,
  wf_cse (Δ ++ [(X, bind_typ (C1 # R1))] ++ Γ) S C ->
  wf_cse (Δ ++ [(X, bind_typ (C2 # R2))] ++ Γ) S C.
Proof with simpl_env; eauto.
  intros.
  remember (Δ ++ [(X, bind_typ (C1 # R1))] ++ Γ).
  generalize dependent Δ.
  induction H; intros F Heq; subst...
  EnvImpl.destruct_binds_hyp H...
Qed.

Lemma wf_cse_ignores_typ_bindings : forall Γ Δ x C1 R1 C2 R2 C S,
  wf_cse (Δ ++ [(x, bind_typ (C1 # R1))] ++ Γ) S C ->
  wf_cse (Δ ++ [(x, bind_typ (C2 # R2))] ++ Γ) S C.
Admitted.
(* Proof with eauto.
  intros*.
  intros H.
  dependent induction H; auto.
  - EnvImpl.destruct_binds_hyp H.
    -- apply (wf_cse_term_fvar T S (Δ ++ [(x, bind_typ (C2 # R2))] ++ Γ) x0).
       apply EnvImpl.binds_app_3; auto.
    -- apply (wf_cse_term_fvar (C2 # R2) S (Δ ++ [(x0, bind_typ (C2 # R2))] ++ Γ) x0).
       auto.
    -- apply (wf_cse_term_fvar T S (Δ ++ [(x, bind_typ (C2 # R2))] ++ Γ) x0).
       auto.
  - apply wf_cse_term_loc with (T := T)...
  - constructor...
Qed.  *)

Lemma wf_cse_ignores_sub_bindings : forall Γ Δ x R1 R2 C S,
  wf_cse (Δ ++ [(x, bind_sub R1)] ++ Γ) S C ->
  wf_cse (Δ ++ [(x, bind_sub R2)] ++ Γ) S C.
Admitted.
(* Proof with eauto.
  intros * H.
  dependent induction H; auto.
  - EnvImpl.destruct_binds_hyp H.
    -- apply (wf_cse_term_fvar T S (Δ ++ [(x, bind_sub R2)] ++ Γ) x0).
       apply EnvImpl.binds_app_3... auto.
    -- apply (wf_cse_term_fvar T S (Δ ++ [(x, bind_sub R2)] ++ Γ) x0).
       auto.
  - apply wf_cse_term_loc with (T := T)...
  - constructor...
Qed.  *)

Create HintDb fsetdec.

Hint Extern 1 (_ `in`A _) => fsetdec: fsetdec.

(* skip this *)
(* Lemma wf_cset_singleton_by_mem : forall xs b1 Γ x b2,
  Γ ⊢ₛ (cset_set xs {}N b1) wf ->
  x `in` xs ->
  Γ ⊢ₛ (cset_set {x}A {}N b2) wf.
Proof with eauto with fsetdec.
  intros * Wfxs xIn.
  inversion Wfxs; subst...
  constructor...
  intros y yIn; assert (y = x) by (clear - yIn; fsetdec); subst; clear yIn.
  rename select (allbound _ _) into Hb.
  apply (Hb x ltac:(fsetdec)).
Qed.

(* NOTE: wf_cset precondition in wf_cset_singleton_by_mem0 can be proven by
         constructor, which leaves an uninstantiated evar. This approach avoids the
         problem. *)
Hint Extern 1 (wf_cset ?Γ (cset_set {?x}A {}N _ _)) =>
match goal with
| H1 : x `in` ?xs , H2 : (wf_cset ?Γ (cset_set ?xs {}N ?b ?ls)) |- _ =>
  apply (wf_cset_singleton_by_mem xs b ls)
end : core.

Local Lemma __test_wf_cset_singleton2 : forall xs b1 Γ x b2,
  Γ ⊢ₛ (cset_set xs {}N b1) wf ->
  x `in` xs ->
  Γ ⊢ₛ (cset_set {x}A {}N b2) wf.
Proof with eauto*.
  intros.
  constructor.
  intros x' x'_in_x.
  assert (x' = x) by fsetdec; subst.
  inversion H; subst...
Qed.

Local Lemma __test_wf_cset_singleton1 : forall xs b1 Γ x b2,
  Γ ⊢ₛ (cset_set xs {}N b1) wf ->
  x `in` xs ->
  Γ ⊢ₛ (cset_set {x}A {}N b2) wf.
Proof.
  eauto using __test_wf_cset_singleton2.
Qed. *)

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

Ltac wf_typ_inversion H :=
  inversion H;
  let t := type of H in
  let has_useful_wf_pretyp :=
      fun T =>
        match T with
        | (typ_arr _ _) => true
        | (typ_all _ _) => true
        | _ => false
        end
  in
  let invert_pure_typ :=
      fun Γ T S =>
        match goal with
        | H : wf_typ Γ S T |- _ =>
          inversion H
        end
  in
  match t with
  | wf_typ ?Γ ?S (_ # ?T) =>
    match has_useful_wf_pretyp T with
    | true => invert_pure_typ Γ T
    | false => idtac
    end
  | _ => idtac
  end; subst.

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_typ : forall Γ T S,
  wf_typ Γ S T ->
  type T.
Proof with eauto using cset_from_wf_cse.
  intros * H.
  induction H...
Qed.

Tactic Notation "solve_obvious" "with" ident(id) :=
  try solve [econstructor; eauto using id].

Lemma wf_cse_strengthen : forall x Γ Δ C U S,
  x ∉ (cse_fvars C) ->
  wf_cse (Δ ++ [(x, bind_typ U)] ++ Γ) S C ->
  wf_cse (Δ ++ Γ) S C.
Admitted.
(* Proof with eauto.
  intros * ? H.
  dependent induction H...
  - destruct (x == x0); simpl in H0; notin_simpl...
    + contradiction (H2 e).
    + econstructor. EnvImpl.destruct_binds_hyp H...
  - apply wf_cse_union...
    + rewrite cse_fvars_join_union in H0.
      notin_simpl...
    + rewrite cse_fvars_join_union in H0.
      notin_simpl...
Qed. *)

Lemma notin_open_tt_rec_fv_ct : forall k x T U,
  x ∉ (fv_ct T `union`A fv_ct U) ->
  x ∉ fv_ct (open_tt_rec k U T).
Admitted.
(* Proof with eauto*.
  intros * NotIn.
  generalize dependent k.
  induction T; intros k; simpl in *...
  induction U; unfold open_vt; destruct v; simpl...
  all: destruct (k === n); simpl; simpl in NotIn...
Qed. *)

Lemma notin_open_cse : forall k x c d,
  x ∉ ((cse_fvars c) `union`A (cse_fvars d)) ->
  x ∉ (cse_fvars (open_cse k c d)).
Admitted.
(* Proof with eauto*.
  intros * NotIn.
  induction d; simpl in *...
  destruct (k === n); simpl in *...
Qed. *)

Lemma notin_open_ct_rec_fv_ct : forall k x c T,
  x ∉ (fv_ct T `union`A (cse_fvars c)) ->
  x ∉ fv_ct (open_ct_rec k c T).
Admitted.
(* Proof with eauto using notin_open_cse.
  intros * NotIn.
  generalize dependent k.
  induction T; intros k; simpl in *...
Qed. *)

Lemma wf_typ_strengthen : forall x Γ Δ T U S,
  x ∉ (EnvImpl.dom Δ `union`A fv_ct T) ->
  wf_typ (Δ ++ [(x, bind_typ U)] ++ Γ) S T ->
  wf_typ (Δ ++ Γ) S T.
Admitted.
(* Proof with eauto*.
  intros * NotIn WfT.
  eremember (Δ ++ [(x, bind_typ U)] ++ Γ) as Ctx.
  generalize dependent Δ.
  induction WfT; intros Ctx NotIn EQ; subst; simpl in *; notin_simpl; simpl_env in *.
  - EnvImpl.destruct_binds_hyp H; simpl in *; notin_simpl...
  - apply wf_typ_top.
  - pick fresh y and apply wf_typ_arr...
    rewrite_env (([(y, bind_typ (C # R))] ++ Ctx) ++ Γ).
    assert (x <> y) by (clear - Fr; fsetdec).
    apply H0.
    + fsetdec.
    + repeat rewrite dom_concat; simpl.
      repeat apply notin_union...
      apply notin_open_ct_rec_fv_ct...
    + auto.
  - pick fresh Y and apply wf_typ_all...
    rewrite_env (([(Y, bind_sub R)] ++ Ctx) ++ Γ).
    assert (x <> Y) by (clear - Fr; fsetdec).
    apply H1.
    + fsetdec.
    + repeat rewrite dom_concat; simpl.
      repeat apply notin_union...
      apply notin_open_tt_rec_fv_ct...
    + auto.
  - auto.
  - apply wf_typ_capt...
    eapply wf_cse_strengthen...
Qed. *)

Lemma wf_typ_weakening : forall T Γ Θ Δ S,
  wf_typ (Δ ++ Γ) S T ->
  EnvImpl.ok (Δ ++ Θ ++ Γ) ->
  wf_typ (Δ ++ Θ ++ Γ) S T.
Admitted.
(* Proof with eauto*.
  intros * Hwf Hok.
  eremember (Δ ++ Γ) as Ctx.
  generalize dependent Δ.
  induction Hwf; intros Δ EQ Hok; subst...
  - pick fresh x and apply wf_typ_arr...
    rewrite_env (([(x, bind_typ (C # R))] ++ Δ) ++ Θ ++ Γ).
    apply H0...
    apply ok_cons...
  - pick fresh X and apply wf_typ_all...
    rewrite_env (([(X, bind_sub R)] ++ Δ) ++ Θ ++ Γ).
    apply H1...
    apply ok_cons...
  - apply wf_typ_capt...
    apply wf_cse_weakening...
Qed. *)

Lemma wf_typ_weaken_head : forall T Γ Δ S,
  wf_typ Γ S T ->
  EnvImpl.ok (Δ ++ Γ) ->
  wf_typ (Δ ++ Γ) S T.
Proof.
  intros.
  rewrite_env (nil ++ Δ ++ Γ).
  apply wf_typ_weakening; eauto || fsetdec.
Qed.

Lemma wf_typ_ignores_sub_bindings : forall V U T Γ Δ X S,
  wf_typ (Δ ++ [(X, bind_sub V)] ++ Γ) S T ->
  wf_typ (Δ ++ [(X, bind_sub U)] ++ Γ) S T.
Proof with simpl_env; eauto using wf_cse_ignores_sub_bindings.
  intros.
  remember (Δ ++ [(X, bind_sub V)] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Heq; subst...
  - Case X0.
    EnvImpl.destruct_binds_hyp H...
  - (* - Case "∀ (S) T". *)
    pick fresh y and apply wf_typ_arr...
    rewrite_env (([(y, bind_typ (C # R))] ++ Δ) ++ [(X, bind_sub U)] ++ Γ).
    apply H1...
  - (* - Case "∀ [R] T". *)
    pick fresh Y and apply wf_typ_all...
    rewrite_env (([(Y, bind_sub R)] ++ Δ) ++ [(X, bind_sub U)] ++ Γ).
    apply H2...
Qed.

Lemma wf_typ_ignores_typ_bindings : forall C1 R1 C2 R2 T Γ Δ x S,
  wf_typ (Δ ++ [(x, bind_typ (C1 # R1))] ++ Γ) S T ->
  wf_typ (Δ ++ [(x, bind_typ (C2 # R2))] ++ Γ) S T.
Admitted.
(* Proof with simpl_env; eauto using wf_cse_ignores_typ_bindings.
  intros.
  remember (Δ ++ [(x, bind_typ (C1 # R1))] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Heq; subst...
  - (* - Case "X0". *)
    EnvImpl.destruct_binds_hyp H...
  - (* - Case "∀ (S) T". *)
    pick fresh y and apply wf_typ_arr...
    rewrite_env (([(y, bind_typ (C # R))] ++ Δ) ++ [(x, bind_typ (C2 # R2))] ++ Γ).
    apply H1...
  - (* - Case "∀ [R] T". *)
    pick fresh Y and apply wf_typ_all...
    rewrite_env (([(Y, bind_sub R)] ++ Δ) ++ [(x, bind_typ (C2 # R2))] ++ Γ).
    apply H2...
Qed. *)

Notation "x `mem`A E" := (AtomSetImpl.mem x E) (at level 69) : metatheory_scope.

(* ********************************************************************** *)
(** * #<a name="wffrom"></a># Lemmas helping to extract wellformedness or closedness from other properties. *)


Lemma wf_typ_from_binds_typ : forall x U Γ S,
  wf_ctx Γ S ->
  EnvImpl.binds x (bind_typ U) Γ ->
  wf_typ Γ S U.
Admitted.
(* Proof with eauto using wf_typ_weaken_head.
  intros * Hwf Hbinds.
  induction Hwf; EnvImpl.destruct_binds_hyp Hbinds...
  inversion H3; subst...
Qed. *)

Lemma wf_typ_from_binds_sub : forall x U Γ S,
  wf_ctx Γ S ->
  EnvImpl.binds x (bind_sub U) Γ ->
  wf_typ Γ S U.
Admitted.
(* Proof with eauto using wf_typ_weaken_head.
  intros x U E S Hwf Hbinds.
  induction Hwf; EnvImpl.destruct_binds_hyp Hbinds...
  rename select (_ = _) into EQ.
  inversion EQ; subst...
Qed. *)

Lemma wf_typ_from_wf_ctx_typ : forall x T Γ S,
  wf_ctx ([(x, bind_typ T)] ++ Γ) S ->
  wf_typ Γ S T.
Proof.
  intros * H; inversion H; auto.
Qed.

Lemma wf_cse_from_binds : forall C R x Γ S,
  wf_ctx Γ S ->
  EnvImpl.binds x (bind_typ (C # R)) Γ ->
  wf_cse Γ S (cse_fvar x).
Proof.
  intros.
  econstructor.
  instantiate (1 := (C # R)).
  exact H0.
Qed.

Lemma wf_cse_loc_from_binds : forall C R l Γ S,
  wf_ctx Γ S ->
  StoreImpl.binds l (C # R) S ->
  wf_cse Γ S (cse_loc l).
Proof.
  intros.
  econstructor.
  instantiate (1 := (C # R)).
  exact H0.
Qed.

Lemma wf_typ_ctx_bind_typ : forall x U Γ S,
  wf_ctx Γ S ->
  EnvImpl.binds x (bind_typ U) Γ ->
  exists C R, U = C # R /\ wf_typ Γ S (C # R).
Admitted.
(* Proof with eauto using wf_typ_weaken_head.
  intros * WfCtx Binds.
  induction WfCtx.
  - inversion Binds.
  - EnvImpl.destruct_binds_hyp Binds.
    rename select (binds x _ _) into Binds.
    destruct (IHWfCtx Binds) as [C [R [EQ WfCR]]].
    exists C, R.
    split...
  - EnvImpl.destruct_binds_hyp Binds.
    + rename select (binds x _ _) into Binds.
      destruct (IHWfCtx Binds) as [D [Q [EQ WfCR]]].
      exists D, Q.
      split...
    + exists C, R.
      inversion select (bind_typ _ = bind_typ _).
      split...
Qed. *)

Lemma wf_typ_ctx_bind_sub : forall X U Γ S,
  wf_ctx Γ S ->
  EnvImpl.binds X (bind_sub U) Γ ->
  pure_type U /\ wf_typ Γ S U.
Admitted.
(* Proof with eauto using wf_typ_weaken_head. 
  intros * WfCtx Binds.
  induction WfCtx.
  - inversion Binds.
  - EnvImpl.destruct_binds_hyp Binds.
    + rename select (binds X _ _) into Binds.
      destruct (IHWfCtx Binds) as [PureU WfU].
      split...
    + inversion select (bind_sub _ = bind_sub _).
      split... 
  - EnvImpl.destruct_binds_hyp Binds.
    rename select (binds X _ _) into Binds.
    destruct (IHWfCtx Binds) as [PureU WfU].
    split...
Qed. *)

(* Hint Resolve wf_cv_ctx_bind_typ : core. *)
Hint Resolve wf_typ_ctx_bind_typ : core.
Hint Resolve wf_typ_ctx_bind_sub : core.

(* ********************************************************************** *)
(** * #<a name="wfsubst"></a># Lemmas connecting substitution and wellformedness of [wf_cset], [wf_typ], ... *)

Ltac destruct_union_mem H :=
  rewrite AtomSetFacts.union_iff in H; destruct H as [H|H].

(* REVIEW: there is something weird with subst_tb:
  - subst_tb X (C # P) (bind_sub X) = bind_sub (C # P)
  - subst_tb X P (bind_typ X) = bind_typ P
  breaks the invariant that P in bind_sub P is a pure type
  and T in bind_typ T is not a captured type.
  Possible solution: make bind_typ take a captured type like
  bind_typ C P instead of bind_typ (C # P), and force the second
  argument of subst_tb to be a pure type.
 *)
Lemma wf_cse_subst_tb : forall Γ Δ Q Z P C S,
  wf_cse (Δ ++ [(Z, bind_sub Q)] ++ Γ) S C ->
  wf_typ Γ S P ->
  wf_cse (EnvImpl.map (subst_tb Z P) Δ ++ Γ) S C.
Admitted.
(* Proof with simpl_env; eauto*.
  intros * HwfC HwfP.
  dependent induction HwfC; auto...
  - EnvImpl.destruct_binds_hyp H.
    -- apply (wf_cse_term_fvar T S (EnvImpl.map (subst_tb Z P) Δ ++ Γ) x)...
    -- apply (wf_cse_term_fvar (subst_tt Z P T) S (map (subst_tb Z P) Δ ++ Γ) x)...
Qed. *)

Lemma wf_cse_over_subst : forall Γ Δ Q Z C C' S,
  EnvImpl.ok (EnvImpl.map (subst_cb Z C) Δ ++ Γ) ->
  wf_cse Γ S C ->
  wf_cse (Δ ++ [(Z, bind_typ Q)] ++ Γ) S C' ->
  EnvImpl.ok (Δ ++ [(Z, bind_typ Q)] ++ Γ) ->
  wf_cse (EnvImpl.map (subst_cb Z C) Δ ++ Γ) S (subst_cse Z C C').
Admitted.
(* Proof with eauto*.
  intros Γ Δ Q Z C C' S.
  intros HokFE HwfC HwfC' Hok.
  induction C'; simpl; eauto*.
  - inversion HwfC'.
  - destruct (Z == a).
    + apply wf_cse_weaken_head; auto.
    + dependent induction HwfC'. EnvImpl.destruct_binds_hyp H.
      -- apply (wf_cse_term_fvar T S (map (subst_cb Z C) Δ ++ Γ) a)...
      -- apply (wf_cse_term_fvar (subst_ct Z C T) S (map (subst_cb Z C) Δ ++ Γ) a)...
  - inversion HwfC'. apply wf_cse_term_loc with (T := T)...
  - apply wf_cse_over_join in HwfC'...
Qed. *)

Lemma wf_typ_subst_cb : forall Γ Δ Q Z C T S,
  wf_typ (Δ ++ [(Z, bind_typ Q)] ++ Γ) S T ->
  wf_cse Γ S C ->
  EnvImpl.ok (EnvImpl.map (subst_cb Z C) Δ ++ Γ) ->
  EnvImpl.ok (Δ ++ [(Z, bind_typ Q)] ++ Γ) ->
  wf_typ (EnvImpl.map (subst_cb Z C) Δ ++ Γ) S (subst_ct Z C T).
Admitted.
(* Proof with simpl_env;
           eauto using wf_typ_weaken_head,
                       wf_cse_subst_tb,
                       type_from_wf_typ,
                       cset_from_wf_cse.
  intros *.
  intros HwfT HwfC Hok HokZ.
  remember (Δ ++ [(Z, bind_typ Q)] ++ Γ).
  generalize dependent Δ.
  induction HwfT; intros Δ ? Hok; subst; simpl subst_ct...
  - (* - Case "X". *)
    assert (X <> Z). {
      EnvImpl.destruct_binds_hyp H...
      - simpl_env in *.
        notin_solve.
      - assert (binds X (bind_sub T) (Δ ++ [(Z, bind_typ Q)] ++ Γ)) by auto.
        forwards: fresh_mid_head HokZ.
        forwards: binds_In H1.
        fsetdec.
    }
    EnvImpl.destruct_binds_hyp H...
    apply (wf_typ_var _ S X (subst_ct Z C T))...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr.
    + fold subst_ct...
    + unfold open_ct in *...
      rewrite <- subst_ct_open_ct_rec.
      2-4: eauto.
      rewrite_env (map (subst_cb Z C) ([(y, bind_typ (C0 # R))] ++ Δ) ++ Γ).
      apply H0...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all.
    + fold subst_ct...
    + apply subst_ct_pure_type...
    + rewrite subst_ct_open_tt_var.
      2-3: eauto.
      rewrite_env (map (subst_cb Z C) ([(Y, bind_sub R)] ++ Δ) ++ Γ).
      apply H1...
  - Case "C # R".
    apply wf_typ_capt.
    + apply wf_cse_over_subst with (Q := Q)...
    + apply IHHwfT...
    + apply subst_ct_pure_type...
    Unshelve.
Qed. *)

Lemma wf_cse_subst_cb : forall Γ Δ Q x C D S,
  wf_cse (Δ ++ [(x, bind_typ Q)] ++ Γ) S C ->
  wf_ctx (Δ ++ [(x, bind_typ Q)] ++ Γ) S ->
  wf_cse Γ S D ->
  wf_cse (EnvImpl.map (subst_cb x D) Δ ++ Γ) S (subst_cse x D C).
Admitted.
(* Proof with simpl_env; eauto*.
  intros * HwfC HwfCtx HwfD.
  induction C; eauto*.
  - inversion HwfC.
  - simpl. destruct (x == a).
    + apply wf_cse_weaken_head... apply ok_from_wf_ctx in HwfCtx...
    + dependent induction HwfC.
      EnvImpl.destruct_binds_hyp H...
      apply (wf_cse_term_fvar (subst_ct x D T) S (map (subst_cb x D) Δ ++ Γ) a)...
  - inversion HwfC. apply wf_cse_term_loc with (T := T)...
  - simpl. apply wf_cse_over_join in HwfC...
Qed. *)

Lemma wf_typ_open_cse : forall Γ C R T S,
  EnvImpl.ok Γ ->
  wf_typ Γ S (∀ (R) T) ->
  wf_cse Γ S C ->
  wf_typ Γ S (open_ct T C).
Admitted.
(* Proof with simpl_env; eauto.
  intros * Hok HwfA HwfC.
  inversion HwfA; subst...
  pick fresh x.
  rewrite (subst_ct_intro x)...
  rewrite_env (map (subst_cb x C) nil ++ Γ).
  eapply wf_typ_subst_cb with (Q := C0 # R0)...
Qed. *)

Lemma wf_typ_subst_tb : forall Γ Δ Q Z P T S,
  wf_typ (Δ ++ [(Z, bind_sub Q)] ++ Γ) S T ->
  (** NOTE here that P needs to be well formed in both the + and - environments, *)
(*       as we're substituting in both places. *)
  wf_typ Γ S P ->
  pure_type P ->
  EnvImpl.ok (Δ ++ [(Z, bind_sub Q)] ++ Γ) ->
  wf_typ (EnvImpl.map (subst_tb Z P) Δ ++ Γ) S (subst_tt Z P T).
Admitted.
  (* Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ, wf_cse_subst_tb.
  intros * HwfT HwfP HpureP Hok.
  (* remember (F ++ [(Z, bind_sub Q)] ++ E). *)
  (* generalize dependent F. *)
  (* induction HwfT; intros F EQF Hok; subst; simpl subst_tt. *)
  dependent induction HwfT; simpl...
  - (* - Case "X". *)
    destruct (X == Z); subst.
    + SCase "X == Z".
      eapply wf_typ_weaken_head...
    + SCase "X <> Z".
      forwards: fresh_mid_tail Hok.
      EnvImpl.destruct_binds_hyp H.
      * applys wf_typ_var T...
      * applys wf_typ_var (subst_tt Z P T)...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr...
    unfold open_ct in *...
    rewrite <- subst_tt_open_ct_rec...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ (C # R))] ++ Δ) ++ Γ).
    eapply H0...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all...
    unfold open_ct in *...
    1: apply subst_tt_pure_type...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub R)] ++ Δ) ++ Γ).
    eapply H1...
  - Case "C # R".
    simpl.
    apply wf_typ_capt...
    assert (wf_typ (map (subst_tb Z P) Δ ++ Γ) S (subst_tt Z P R)) by (eapply IHHwfT; eauto* ).
    apply subst_tt_pure_type...
Qed. *)

Lemma wf_typ_open_type : forall Γ U R T S,
  EnvImpl.ok Γ ->
  wf_typ Γ S (∀ [R] T) ->
  wf_typ Γ S U ->
  pure_type U ->
  wf_typ Γ S (open_tt T U).
Admitted.
(* Proof with simpl_env; eauto.
  intros * Hok HwfA HwfU HpureU.
  inversion HwfA; subst...
  pick fresh X.
  rewrite (subst_tt_intro X)...
  assert (X ∉ dom Γ) by notin_solve.
  rewrite_env (map (subst_tb X U) nil ++ Γ).
  apply wf_typ_subst_tb with (Q := R)...
Qed. *)

Lemma wf_ctx_subst_tb : forall Γ Δ Q Z P S,
  wf_ctx (Δ ++ [(Z, bind_sub Q)] ++ Γ) S ->
  wf_typ Γ S P ->
  pure_type P ->
  wf_ctx (EnvImpl.map (subst_tb Z P) Δ ++ Γ) S.
Admitted.
(* Proof with eauto 6 using wf_typ_subst_tb.
  induction Δ; intros * WfCtx WfP HpureP; simpl...
  inversion WfCtx; subst; simpl subst_tb; simpl_env in *.
  - apply wf_ctx_sub.
    + eapply IHΔ...
    + eapply wf_typ_subst_tb...
    + apply subst_tt_pure_type... 
    + rewrite dom_concat, dom_map...
  - apply wf_ctx_typ.
    + eapply IHΔ...
    + replace (C # subst_tt Z P R) with (subst_tt Z P (C # R)) by reflexivity.
      eapply wf_typ_subst_tb...
    + rewrite dom_concat, dom_map...
Qed. *)

Lemma wf_ctx_subst_cb : forall Γ Δ Q C x S,
  wf_ctx (Δ ++ [(x, bind_typ Q)] ++ Γ) S ->
  wf_cse Γ S C ->
  wf_ctx (EnvImpl.map (subst_cb x C) Δ ++ Γ) S.
Admitted.
(* Proof with eauto using wf_typ_subst_cb.
  intros *.
  induction Δ; intros Hwf HwfC...
  simpl.
  inversion Hwf; subst; simpl subst_cb; simpl_env in *.
  - apply wf_ctx_sub.
    + eapply IHΔ...
    + eapply wf_typ_subst_cb...
    + apply subst_ct_pure_type...
    + rewrite dom_concat, dom_map...
  - apply wf_ctx_typ.
    + eapply IHΔ...
    + replace (subst_cse x C C0 # subst_ct x C R) with (subst_ct x C (C0 # R)) by reflexivity.
      eapply wf_typ_subst_cb...
    + rewrite dom_concat, dom_map...
Qed. *)

(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_ctx] *)

Lemma wf_ctx_narrowing : forall Γ Δ V U X S,
  wf_ctx (Δ ++ [(X, bind_sub V)] ++ Γ) S ->
  pure_type U ->
  wf_typ Γ S U ->
  wf_ctx (Δ ++ [(X, bind_sub U)] ++ Γ) S.
Admitted.
  (* Proof with eauto using wf_typ_ignores_sub_bindings, wf_typ_ignores_typ_bindings.
  induction Δ; intros * WfCtx Wf;
    inversion WfCtx; subst; simpl_env in *...
Qed. *)

Lemma wf_ctx_narrowing_typ : forall Γ Δ C1 R1 C2 R2 X S,
  wf_ctx (Δ ++ [(X, bind_typ (C1 # R1))] ++ Γ) S ->
  wf_typ Γ S (C2 # R2) ->
  wf_ctx (Δ ++ [(X, bind_typ (C2 # R2))] ++ Γ) S.
Admitted.
(* Proof with eauto using wf_typ_ignores_sub_bindings, wf_typ_ignores_typ_bindings.
  induction Δ; intros * WfCtx Wf;
    inversion WfCtx; subst; simpl_env in *...
Qed. *)

Lemma ok_from_wf_store_ctx : forall S,
  wf_store_ctx S ->
  StoreImpl.ok S.
Admitted.
(* Proof with eauto.
  intros * H.
  induction H...
Qed. *)

Hint Resolve ok_from_wf_store_ctx : core.

Lemma wf_store_ctx_from_wf_ctx : forall S Γ,
  wf_ctx Γ S ->
  wf_store_ctx S.
Proof with eauto.
  intros * H.
  induction H...
Qed.

Hint Resolve wf_store_ctx_from_wf_ctx : core.

Lemma wf_cse_weaken_store_tail: forall C Γ S1 S2,
  wf_cse Γ S2 C ->
  StoreImpl.ok (S1 ++ S2) ->
  wf_cse Γ (S1 ++ S2) C.
Proof with eauto.
  intros * Hwf Hok.
  induction Hwf...
Qed.

Lemma wf_typ_weaken_store_tail: forall T Γ S1 S2,
  wf_typ Γ S2 T ->
  StoreImpl.ok (S1 ++ S2) ->
  wf_typ Γ (S1 ++ S2) T.
Proof with eauto.
  intros * Hwf Hok.
  induction Hwf...
  apply wf_typ_capt...
  apply wf_cse_weaken_store_tail...
Qed.

Lemma wf_store_ctx_strengthen : forall S1 S2,
  wf_store_ctx (S1 ++ S2) ->
  wf_store_ctx S2.
Admitted.
(* Proof with eauto.
  intros * H.
  induction S1...
  destruct a.
  rewrite (StoreImpl.cons_app_assoc _ l t S1 S2) in H.
  inversion H; subst...
Qed. *)

Lemma wf_typ_from_wf_store_ctx_nil : forall S C R l,
  wf_store_ctx S ->
  StoreImpl.binds l (C # R) S ->
  wf_typ nil S (C # R).
Admitted.
(* Proof with eauto 5 using wf_typ_weaken_store_tail.
  intros * Hwf Hbinds.
  induction Hwf...
  - inversion Hbinds.
  - inversion Hbinds.
    destruct (l === l0); subst...
    inversion H2; subst...
Qed. *)

Lemma wf_typ_from_wf_store_ctx : forall Γ S C R l,
  wf_store_ctx S ->
  StoreImpl.binds l (C # R) S ->
  wf_ctx Γ S ->
  wf_typ Γ S (C # R).
Proof with eauto 5 using wf_typ_weaken_store_tail.
  intros * Hwf Hbinds WfCtx.
  enough (wf_typ nil S (C # R)) as H.
  apply wf_typ_weaken_head with (Δ := Γ) in H; simpl_env in *...

  apply wf_typ_from_wf_store_ctx_nil with (l := l)...
Qed.

Lemma wf_pair_from_wf_store_ctx : forall Γ S C R l,
  wf_store_ctx S ->
  wf_ctx Γ S ->
  StoreImpl.binds l (C # R) S ->
  wf_cse Γ S C /\ wf_typ Γ S (C # R).
Proof with eauto.
  intros * Hwf HwfCtx Hbinds.
  epose proof (wf_typ_from_wf_store_ctx Γ S C R l Hwf Hbinds HwfCtx) as H.
  inversion H; subst...
Qed.

Lemma wf_cse_weakening_store : forall Γ S1 S2 S3 C,
  wf_cse Γ (S1 ++ S3) C ->
  wf_store_ctx (S1 ++ S2 ++ S3) ->
  wf_cse Γ (S1 ++ S2 ++ S3) C.
Proof with eauto.
  intros * Hwf Hok.
  dependent induction Hwf...
Qed.

Lemma wf_typ_weakening_store : forall Γ S1 S2 S3 T,
  wf_typ Γ (S1 ++ S3) T ->
  wf_store_ctx (S1 ++ S2 ++ S3) ->
  wf_typ Γ (S1 ++ S2 ++ S3) T.
Proof with eauto.
  intros * Hwf Hok.
  dependent induction Hwf...
  apply wf_typ_capt...
  apply wf_cse_weakening_store...
Qed.

Lemma wf_ctx_weakening_store : forall Γ S1 S2 S3,
  wf_ctx Γ (S1 ++ S3) ->
  wf_store_ctx (S1 ++ S2 ++ S3) ->
  wf_ctx Γ (S1 ++ S2 ++ S3).
Proof with eauto using wf_cse_weakening_store, wf_typ_weakening_store.
  intros * Hwf Hok.
  dependent induction Hwf...
Qed.

