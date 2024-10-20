Require Import Coq.Program.Equality.

Require Export CCsub_Infrastructure.
Require Export CCsub_Wellformedness.
Require Import Atom.

Require Import LibTactics.

(* ********************************************************************** *)
(** * #<a name="notin"></a># Lemmas about free variables and "notin" *)


(** Uniqueness of bindings **)

Lemma binds_unique : forall b1 b2 x (E : env),
  binds x b1 E ->
  binds x b2 E ->
  b1 = b2.
Proof.
  intros* Hb1 Hb2.
  congruence.
Qed.

Lemma binds_typ_unique : forall T1 T2 X E,
  binds X (bind_typ T1) E ->
  binds X (bind_typ T2) E ->
  T1 = T2.
Proof.
  intros* Hb1 Hb2.
  congruence.
Qed.

(** These proofs are all the same, but Coq isn't smart enough unfortunately... *)

Lemma notin_fv_tt_open_tt_rec : forall k (X : atom) U T,
  X ∉ fv_tt (open_tt_rec k U T) ->
  X ∉ fv_tt T.
Proof.
  intros k X U T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
  unfold open_vt in Fr; destruct v; simpl in Fr; fsetdec.
Qed.

Lemma notin_fv_tt_open_tt : forall (X : atom) U T,
  X ∉ fv_tt (open_tt T U) ->
  X ∉ fv_tt T.
Proof with eauto.
  intros. apply notin_fv_tt_open_tt_rec with (k := 0) (U := U)...
Qed.

Lemma notin_cset_fvars_open_cset : forall X k C c,
  X ∉ cse_fvars (open_cse k C c) ->
  X ∉ cse_fvars c.
Proof with auto.
  intros.
  induction c; eauto*.
  simpl. unfold not in H. unfold not. intros. apply H.
  simpl. rewrite AtomSetFacts.union_iff in H0. destruct H0.
  - rewrite AtomSetFacts.union_iff. left.
    induction c1; auto; fsetdec.
  - rewrite AtomSetFacts.union_iff. right.
    induction c1; auto; fsetdec.  
Qed.

Lemma notin_fv_tt_open_ct_rec : forall k (X : atom) C T,
  X ∉ fv_tt (open_ct_rec k C T) ->
  X ∉ fv_tt T.
Proof with eauto using notin_cset_fvars_open_cset.
  intros k Y C T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_tt_open_ct : forall (X : atom) C T,
  X ∉ fv_tt (open_ct T C) ->
  X ∉ fv_tt T.
Proof with eauto.
  intros. apply notin_fv_tt_open_ct_rec with (k := 0) (C := C)...
Qed.

Lemma notin_fv_ct_open_tt_rec : forall k (X : atom) U T,
  X ∉ fv_ct (open_tt_rec k U T) ->
  X ∉ fv_ct T.
Proof with eauto using notin_cset_fvars_open_cset.
  intros k X U T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union...
Qed.

Lemma notin_fv_ct_open_tt : forall (X : atom) U T,
  X ∉ fv_ct (open_tt T U) ->
  X ∉ fv_ct T.
Proof with eauto*.
  intros. apply notin_fv_ct_open_tt_rec with (k := 0) (U := U)...
Qed.

Lemma notin_fv_ct_open_ct_rec : forall (X : atom) T C k,
  X ∉ fv_ct (open_ct_rec k C T) ->
  X ∉ fv_ct T.
Proof with auto.
  intros X T C.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - apply IHT1 with (k := k)...
  - apply IHT2 with (k := S k)...
  - apply IHT1 with (k := k)...
  - apply IHT2 with (k := S k)... 
  - apply notin_cset_fvars_open_cset with (k := k) (C := C)...
  - apply IHT with (k := k)...
Qed.

Lemma notin_fv_ct_open_ct : forall (X : atom) T C,
  X ∉ fv_ct (open_ct T C) ->
  X ∉ fv_ct T.
Proof with auto.
  intros. apply notin_fv_ct_open_ct_rec with (k := 0) (C := C)...
Qed.

Lemma notin_fv_wf_cse : forall Γ (x : atom) C,
  Γ ⊢ₛ C wf ->
  x ∉ dom Γ ->
  x ∉ `cse_fvars` C.
Proof with eauto*.
  intros * WfC NotIn.
  dependent induction WfC; eauto*.
  destruct (x == x0).
  - exfalso. subst. apply binds_In in H...
  - auto. 
Qed.

Lemma notin_fv_wf_typ : forall Γ (X : atom) T,
  Γ ⊢ T wf ->
  X ∉ dom Γ ->
  X ∉ (fv_tt T `u`A fv_ct T).
Proof with eauto using notin_fv_wf_cse.
  intros * WfT.
  induction WfT; intros NotIn; simpl.
  - Case "wf_typ_var".
    rename select (binds _ _ _) into Binds.
    enough (X <> X0) by fsetdec.
    enough (X0 ∈ dom Γ) by fsetdec.
    applys binds_In Binds.
  - Case "⊤".
    fsetdec.
  - Case "∀ (S) T".
    rename select (forall x : atom, x ∉ L -> X ∉ dom _ -> _) into IH.
    pick fresh y and specialize IH.
    rewrite dom_concat in IH; simpl in IH.
    specialize (IH ltac:(notin_solve)).
    destruct (AtomSetNotin.elim_notin_union IH) as [NotInFvTT NotInFvCT].
    apply notin_fv_tt_open_ct in NotInFvTT.
    apply notin_fv_ct_open_ct in NotInFvCT.
    specialize (IHWfT ltac:(notin_solve)).
    simpl in IHWfT.
    clear - NotInFvTT NotInFvCT IHWfT.
    fsetdec.
  - Case "∀ [R] T".
    rename select (forall x : atom, x ∉ L -> X ∉ dom _ -> _) into IH.
    pick fresh Y and specialize IH.
    rewrite dom_concat in IH; simpl in IH.
    specialize (IH ltac:(notin_solve)).
    destruct (AtomSetNotin.elim_notin_union IH) as [NotInFvTT NotInFvCT].
    apply notin_fv_tt_open_tt in NotInFvTT.
    apply notin_fv_ct_open_tt in NotInFvCT.
    specialize (IHWfT ltac:(notin_solve)).
    clear - NotInFvTT NotInFvCT IHWfT.
    fsetdec.
  - Case "□ T".
    auto.
  - Case "C # R".
    specialize (IHWfT NotIn).
    rename select (Γ ⊢ₛ C wf) into WfC.
    assert (X ∉ `cse_fvars` C) by (eapply notin_fv_wf_cse; eauto).
    fsetdec.
Qed.

(* ********************************************************************** *)
(** * #<a name="cvfree"></a># Lemmas about free variables -- in particular properties of [free_for_cv] *)
(** TODO Maybe have a separate file for free_for_cv lemmas **)

(* Lemma var_cv_open : forall v k (y : atom), *)
(*   cse_subset_prop (var_cv v) (var_cv (open_vv k y v)). *)
(* Proof with eauto*. *)
(*   intros. *)
(*   destruct v; simpl... *)
(*   - unfold cse_subset_prop. simpl. fsetdec. *)
(*   - destruct (k === n); unfold cse_subset_prop; simpl; repeat split; fsetdec... *)
(* Qed. *)

(* TODO: Code duplication in this proof *)
(* Lemma exp_cv_open_ve_rec : forall e k (y : atom) C, *)
(*   cse_subset_prop (exp_cv e) (exp_cv (open_ve_rec k y C e)). *)
(* Proof with eauto using var_cv_open, subset_union. *)
(*   intros e. *)
(*   induction e; intros; simpl... *)
(*   - repeat split; simpl; fsetdec. *)
(*   - destruct v; simpl. *)
(*     + induction c; repeat split; simpl; eauto*; try fsetdec; try fnsetdec. *)
(*       -- destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*         simpl in *. *)
(*         fsetdec.  *)
(*       -- destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*         simpl in *. *)
(*         fnsetdec. *)
(*       -- destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*         simpl in *. *)
(*         destruct (`cse_uvar` (remove_all_bvars c1));  *)
(*         destruct (`cse_uvar` (remove_all_bvars c2)); intuition. *)
(*     + destruct (k === n). *)
(*       -- induction c; repeat split; simpl;  *)
(*         eauto*; try fsetdec; try fnsetdec. *)
(*         ++ destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*           simpl in *. *)
(*           fsetdec. *)
(*         ++ destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*           simpl in *. *)
(*           fnsetdec. *)
(*         ++ destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*           simpl in *. *)
(*           destruct (`cse_uvar` (remove_all_bvars c1)); *)
(*           destruct (`cse_uvar` (remove_all_bvars c2)); simpl; intuition.  *)
(*       -- induction c; repeat split; simpl; *)
(*         eauto*; try fsetdec; try fnsetdec. *)
(*         ++ destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*           simpl in *. *)
(*           fsetdec. *)
(*         ++ destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*           simpl in *. *)
(*           fnsetdec. *)
(*         ++ destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*         simpl in *. *)
(*         destruct (`cse_uvar` (remove_all_bvars c1)); *)
(*         destruct (`cse_uvar` (remove_all_bvars c2)); simpl; intuition.  *)
(* Qed. *)

(* Lemma exp_cv_open_te_rec : forall e k (y : atom), *)
(*   cse_subset_prop (exp_cv e) (exp_cv (open_te_rec k y e)). *)
(* Proof with eauto*. *)
(*   assert ( forall c, cse_subset_prop c c ). *)
(*   { intros. induction c; simpl; repeat split; try fsetdec. *)
(*     - destruct IHc1 as [H1 [H2 H3]]. destruct IHc2 as [H1' [H2' H3']]. *)
(*       simpl in *. destruct (`cse_uvar` c1); auto. } *)
(*   induction e; intros; simpl... *)
(*   specialize (IHe1 k y). *)
(*   specialize (IHe2 (`succ` k) y). *)
(*   apply subset_union... *)
(* Qed. *)

Lemma var_cv_subset_fv_vv : forall v,
  `cse_fvars` (var_cv v) `c`A fv_vv v.
Proof with eauto.
  intros v.
  destruct v; simpl; fsetdec.
Qed.

Lemma var_cv_closed : forall v,
  `cse_bvars` (var_cv v) = {}N.
Proof with eauto*.
  destruct v...
Qed.

Lemma exp_cv_subset_fv_ve : forall e,
  `cse_fvars` (exp_cv e) `c`A fv_ve e.
Proof with eauto using var_cv_subset_fv_vv, atomset_subset_union; eauto*.
  induction e; simpl...
  - fsetdec.
  - apply atomset_subset_union...
  induction c; simpl; fsetdec.   
Qed.

Lemma exp_cv_closed : forall e,
  `cse_bvars` (exp_cv e) = {}N.
Proof with eauto using var_cv_closed.
  induction e; simpl...
  - rewrite (var_cv_closed v), (var_cv_closed v0). fnsetdec.
  - rewrite IHe1, IHe2. fnsetdec.
  - rewrite (var_cv_closed v).
    + induction c; simpl; try fnsetdec.
    assert (`cse_bvars` (remove_all_bvars c1) = {}N).
    { assert (NatSet.F.Empty (`cse_bvars` (remove_all_bvars c1) `u`N {}N)).
      { rewrite IHc1. fnsetdec. } fnsetdec. }
    assert (`cse_bvars` (remove_all_bvars c2) = {}N).
    { assert (NatSet.F.Empty (`cse_bvars` (remove_all_bvars c2) `u`N {}N)).
      { rewrite IHc2. fnsetdec. } fnsetdec. }
    rewrite H, H0.
    fnsetdec.
Qed.

Lemma subcset_empty : forall E C,
  E ⊢ wf ->
  E ⊢ₛ C wf ->
  E ⊢ₛ {} <: C.
Proof with eauto*.
  intros.
  apply subcset_bot.
  exact H.
  exact H0.
Qed.

Lemma exp_cv_subst_te_intro : forall X P e,
  exp_cv e = exp_cv (subst_te X P e).
Proof with eauto; try solve [f_equal; eauto].
  intros X P e.
  induction e; simpl; eauto; f_equal...
Qed.

Lemma cse_fvars_cse_open_ve : forall e (k: nat) (x : atom) (Y : atom),
  x `in` (`cse_fvars` (exp_cv e)) ->
  x `in` (`cse_fvars` (exp_cv (open_ve_rec k Y (cse_fvar Y) e))).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k; simpl in *...
  * destruct v... simpl in Hxine. fsetdec.
  * assert (x `in` `cse_fvars` (var_cv v) \/ x `in` `cse_fvars` (var_cv v0)) by fsetdec.
    destruct H.
    destruct v; simpl in *; fsetdec.
    destruct v0; simpl in *; fsetdec.
  * assert (x `in` `cse_fvars` (exp_cv e1) \/ x `in` `cse_fvars` (exp_cv e2)) by fsetdec.
    destruct H...
    ** assert (x ∈ `cse_fvars` (exp_cv (open_ve_rec k Y (cse_fvar Y) e1))). apply (IHe1 H)... fsetdec.
    ** assert (x ∈ `cse_fvars` (exp_cv (open_ve_rec (`succ` k) Y (cse_fvar Y) e2))). apply (IHe2 H)... fsetdec.
  * destruct v; simpl in *; fsetdec...
  * assert (x ∈ `cse_fvars` (remove_all_bvars c) \/ x `in` `cse_fvars` (var_cv v)) by fsetdec.
    destruct H; induction c; destruct v; simpl in *; fsetdec...
Qed.

Lemma remove_all_bvars_fvar_equal : forall c,
 `cse_fvars` (remove_all_bvars c) = `cse_fvars` c.
Proof with eauto.
  intros c.
  induction c; simpl...
  rewrite IHc1, IHc2...
Qed.

Lemma cse_fvars_cse_open_te : forall e (k : nat) (x : atom) (Y : atom),
  x `in` (`cse_fvars` (exp_cv e)) ->
  x `in` (`cse_fvars` (exp_cv (open_te_rec k Y e))).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k; simpl...
  * simpl in Hxine.
    apply AtomSet.F.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSet.F.union_2...
    ** apply AtomSet.F.union_3...
Qed.

Lemma wf_cse_free_vars_bound : forall X C E,
  (wf_cse E C) ->
  (X `in` `cse_fvars` C) ->
  (exists T, binds X (bind_typ T) E).
Proof with eauto.
  intros X C E Hwf Hx.
  induction Hwf; simpl in *; try fsetdec...
  + assert (X = x) by fsetdec. subst. eauto.
  + rewrite AtomSetFacts.union_iff in Hx.
    destruct Hx...
Qed.

Lemma typing_cse_all_bound : forall E e T,
  typing E e T ->
  (forall X, X `in` `cse_fvars` (exp_cv e) ->
    (exists T, binds X (bind_typ T) E)).
Proof with eauto; simpl_env in *.
  intros.
  induction H; simpl in *; simpl_env...
  - replace X with x... fsetdec.
  - pick fresh Y.
    destruct (H2 Y) as [T Binds]...
      eapply cse_fvars_cse_open_ve...
    simpl in Binds.
    apply (binds_remove_mid_cons _ X Y _ _ _ nil) in Binds.
    simpl in Binds.
    exists T...
    auto.
  - rewrite AtomSetFacts.union_iff in H0.
    destruct H0...
  - pick fresh Y.
    rewrite AtomSetFacts.union_iff in H0...
    destruct H0...
    destruct (H2 Y) as [T Binds]...
      eapply cse_fvars_cse_open_ve...
    apply (binds_remove_mid_cons _ X Y _ _ _ nil) in Binds.
    exists T...
    auto.
  - pick fresh Y.
    destruct (H3 Y) as [T Binds]...
      eapply cse_fvars_cse_open_te...
    apply (binds_remove_mid_cons _ X Y _ _ _ nil) in Binds.
    exists T...
    auto.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in H0.
    destruct H0...
    rewrite remove_all_bvars_fvar_equal in H0.
    apply (wf_cse_free_vars_bound X C Γ) in H0...
Qed.

Lemma cset_all_bound_wf : forall E C,
  cset C ->
  (forall X, X `in` `cse_fvars` C -> exists T,
    binds X (bind_typ T) E) ->
  wf_cse E C.
Proof with eauto.
  intros.
  induction H...
  - specialize (H0 X). simpl in H0.
    destruct (H0 ltac:(fsetdec)) as [T Binds].
    apply (wf_cse_term_fvar T).
    exact Binds.
  - rewrite cse_fvars_join_union in H0.
    constructor...
    assert (forall X, X `in` `cse_fvars` Q1 -> exists T, binds X (bind_typ T) E).
    { intros. apply H0. rewrite AtomSetFacts.union_iff. left... }
    specialize (IHcset1 H2).
    exact IHcset1.
    assert (forall X, X `in` `cse_fvars` Q2 -> exists T, binds X (bind_typ T) E).
    { intros. apply H0. rewrite AtomSetFacts.union_iff. right... }
    specialize (IHcset2 H2).
    exact IHcset2.
Qed.

Lemma expr_cset : forall e,
  cset (exp_cv e).
Proof with eauto.
  intros.
  induction e; simpl...
  - destruct v; simpl...
  - destruct v; apply cset_join; destruct v0; simpl...
  - destruct v; simpl...
  - apply cset_join...
    induction c; simpl...
    destruct v; simpl...
Qed.

(** This should be easily true: free variables
    are all bound if a term has a type.... *)
Lemma typing_cv : forall E e C R,
  typing E e (C # R) ->
  wf_cse E (exp_cv e).
Proof with eauto using wf_cset_over_join; eauto*.
  intros * Htyp.
  unshelve epose proof (typing_cse_all_bound E e (C # R) Htyp) as H1...
  apply cset_all_bound_wf...
  apply expr_cset...
Qed.

Lemma bind_typ_notin_fv_tt : forall x S Γ T,
  binds x (bind_typ S) Γ ->
  Γ ⊢ T wf ->
  x ∉ fv_tt T.
Proof with auto.
  intros * Hbnd WfT.
  dependent induction WfT; simpl...
  - apply AtomSetNotin.notin_union...
    pick fresh y and specialize H0.
    eapply notin_fv_tt_open_ct with (C := cse_fvar y).
    apply H0.
    apply binds_tail...
  - apply AtomSetNotin.notin_union...
    pick fresh Y and specialize H1.
    eapply notin_fv_tt_open_tt.
    apply H1.
    apply binds_tail...
Qed.


Lemma wf_cset_notin_fvars : forall x Γ C,
  Γ ⊢ₛ C wf ->
  x ∉ dom Γ ->
  x ∉ (`cse_fvars` C).
Proof with eauto*.
  intros * WfC NotIn.
  induction WfC...
  simpl.
  eapply binds_In in H.
  fsetdec.
Qed.

Lemma wf_typ_notin_fv_ct : forall x Γ T,
  Γ ⊢ T wf ->
  x ∉ dom Γ ->
  x ∉ fv_ct T.
Proof with eauto*.
  intros * WfT NotIn.
  induction WfT; simpl.
  - fsetdec.
  - fsetdec.
  - apply AtomSetNotin.notin_union...
    pick fresh y and specialize H0.
    apply notin_fv_ct_open_ct with (C := cse_fvar y)...
  - apply AtomSetNotin.notin_union...
    pick fresh Y and specialize H1.
    apply notin_fv_ct_open_tt with (U := Y)...
  - apply (IHWfT NotIn).
  - apply AtomSetNotin.notin_union...
    eapply wf_cset_notin_fvars...
Qed.

(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma subcapt_env_wf : forall Γ C D,
  Γ ⊢ₛ C <: D ->
  Γ ⊢ wf.
Proof with eauto.
  intros * SubCapt.
  induction SubCapt...
Qed.

Lemma subcapt_regular : forall Γ C D,
  Γ ⊢ₛ C <: D ->
  Γ ⊢ₛ C wf /\ Γ ⊢ₛ D wf.
Proof with eauto*.
  intros * SubCapt.
  dependent induction SubCapt; subst...
Qed.

Lemma sub_regular : forall Γ S T,
  Γ ⊢ S <: T ->
  Γ ⊢ wf /\ Γ ⊢ S wf /\ Γ ⊢ T wf.
Proof with simpl_env; eauto*.
  intros * Sub.
  induction Sub...
  - Case "sub_capt".
    rename select (_ ⊢ₛ _ <: _) into SubCapt.
    destruct (subcapt_regular _ _ _ SubCapt).
    repeat split...
  - Case "sub_arr".
    repeat split...
    + pick fresh x and apply wf_typ_arr...
      * apply wf_typ_cse...
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rename select (forall x : atom, x ∉ L -> ([(x, bind_typ (C2 # R2))] ++ Γ) ⊢ wf /\ _ /\ _) into IHSsubT.
        rewrite_nil_concat.
        eapply wf_typ_ignores_typ_bindings.
        apply IHSsubT.
        fsetdec.
    + pick fresh x and apply wf_typ_arr...
      * apply wf_typ_cse...
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rewrite_env (∅ ++ [(x, bind_typ (C2 # R2))] ++ Γ).
        eapply wf_typ_ignores_typ_bindings.
        rename select (forall x, _ -> _ /\ _ /\ _) into IHSubT.
        apply IHSubT.
        fsetdec.
  - Case "sub_all".
    repeat split...
    + pick fresh X and apply wf_typ_all...
      rename select (forall x, _ -> _ /\ _ /\ _) into IHSsubT.
      rewrite_nil_concat.
      eapply wf_typ_ignores_sub_bindings.
      apply IHSsubT.
      fsetdec.
    + pick fresh X and apply wf_typ_all...
      rewrite_env (∅ ++ [(X, bind_sub R2)] ++ Γ).
      eapply wf_typ_ignores_sub_bindings.
      rename select (forall x, _ -> _ /\ _ /\ _) into IHSubT.
      apply IHSubT.
      fsetdec.
Qed.

Lemma typing_var_implies_binds : forall Γ (x : atom) T,
  Γ ⊢ x : T ->
  exists C R, binds x (bind_typ (C # R)) Γ.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
Qed.

Lemma subst_cse_cv_var_commutes_with_subst_vv : forall x u v,
  subst_cse x (cse_fvar u) (var_cv v)
  = var_cv (subst_vv x u v).
Proof with eauto*.
  intros.
  destruct v; simpl...
  destruct (x == a); destruct (a == x); simpl...
Qed.

Lemma subst_cse_cv_commutes_with_susbt_ve : forall x u e,
    subst_cse x (cse_fvar u) (exp_cv e)
  = exp_cv (subst_ve x u (cse_fvar u) e).
Proof with auto using subst_cse_cv_var_commutes_with_subst_vv.
  intros.
  induction e; simpl...
  - repeat rewrite <- subst_cse_cv_var_commutes_with_subst_vv...
  - rewrite <- IHe1, <- IHe2...
  - assert ((subst_cse x (cse_fvar u) (remove_all_bvars c)) = remove_all_bvars (subst_cse x (cse_fvar u) c)).
    {
      induction c; simpl...
      - destruct (x == a); destruct (a == x); simpl...
      - rewrite IHc1, IHc2...
    }
    rewrite H, subst_cse_cv_var_commutes_with_subst_vv...
Qed.

Lemma subst_cset_empty : forall x c,
  subst_cse x c {} = {}.
Proof with eauto*.
  intros.
  unfold subst_cse.
  reflexivity.
Qed.

Lemma sub_pure_type : forall Γ S T,
  Γ ⊢ S <: T ->
  pure_type S <-> pure_type T.
Proof with eauto*.
  intros * Sub.
  split.
  - intros PureS.
    induction Sub; inversion PureS; subst...
    + apply IHSub.
      forwards (WfEnv & _ & _): sub_regular Sub.
      applys wf_typ_env_bind_sub...
    + Case "type_arr".
      pick fresh x and apply type_arr.
      * apply type_cse...
        eapply cset_from_wf_cset.
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rename select (forall x : atom, x ∉ L -> _ ⊢ _ <: _) into IHSubCodomain.
        specialize (IHSubCodomain x ltac:(fsetdec)).
        eapply type_from_wf_typ.
        rename select (_ ⊢ _ <: _) into SubT.
        applys sub_regular SubT.
    + Case "type_all".
      pick fresh X and apply type_all...
      rename select (forall X, _ -> _ ⊢ _ <: _) into SubT.
      specialize (SubT X ltac:(fsetdec)).
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
    + Case "type_box".
      apply type_box.
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
  - intros PureT.
    induction Sub; inversion PureT; subst...
    + Case "sub_arr".
      pick fresh x and apply type_arr.
      * apply type_cse...
        eapply cset_from_wf_cset.
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rename select (forall x, _ -> _ ⊢ _ <: _) into SubT.
        specialize (SubT x ltac:(fsetdec)).
        eapply type_from_wf_typ.
        applys sub_regular SubT.
    + Case "type_all".
      pick fresh X and apply type_all...
      rename select (forall x, _ -> _ ⊢ _ <: _) into SubT.
      specialize (SubT X ltac:(fsetdec)).
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
    + Case "type_box".
      apply type_box.
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
Qed.

Lemma sub_capt_type : forall Γ S T,
  Γ ⊢ S <: T ->
  (exists C R, S = C # R) <-> (exists C R, T = C # R).
Proof with eauto*.
  intros * Sub.
  induction Sub; split; intros [C [R EQ]]; try inversion EQ; subst...
  - assert (WfEnv : Γ ⊢ wf) by (applys sub_regular Sub).
    assert (PureU : pure_type U) by (applys wf_typ_env_bind_sub WfEnv H).
    assert (PureCapt : pure_type (C # R)) by (apply (proj1 (sub_pure_type _ _ _ Sub) PureU)).
    inversion PureCapt.
  - inversion select (pure_type (_ # _)). 
Qed.

Lemma typing_regular : forall Γ e T,
  Γ ⊢ e : T ->
  Γ ⊢ wf /\ expr e /\ Γ ⊢ T wf.
Proof with simpl_env; auto*.
  intros * Typ.
  induction Typ.
  - Case "typing_var".
    repeat split...
    rename select (Γ ⊢ wf) into WfEnv.
    rename select (binds _ _ _) into Binds.
    destruct (wf_typ_env_bind_typ _ _ _ WfEnv Binds) as [D [Q [Eq WfCR]]]; symmetry in Eq; inversion Eq; subst; clear Eq.
    inversion WfCR; subst...
    constructor...
    apply (wf_cse_term_fvar (C # R) _ _).
    exact Binds.
  - Case "typing_abs".
    pick fresh y; assert (y ∉ L) by fsetdec...
    rename select (forall x, _ -> _ /\ _ /\ _) into IH.
    unshelve epose proof (IH y _) as IHy...
    inversion IHy as [Henv [Hexpr Hwf]]...
    repeat split...
    + inversion Henv...
    + pick fresh x and apply expr_abs.
      * eapply type_from_wf_typ.
        eapply wf_typ_from_wf_env_typ.
        apply Henv.
      * destruct (IH x)...
    + constructor...
      eapply typing_cv with (e := (λ (C # R) e1)) (C := exp_cv e1) (R := ∀ (C # R) T1)...
      * apply typing_abs with (L := L)...
      * eapply wf_typ_arr...
        apply IH.
      * apply type_from_wf_typ in H.
        pick fresh x and apply type_arr...
        eapply type_from_wf_typ with (Γ := [(x, bind_typ (C # R))] ++ Γ).
        apply IH.
        fsetdec.
  - Case "typing_app".
    destruct IHTyp1 as [_ [_ Hwf]].
    inversion Hwf; rename select (_ ⊢ _ wf) into HwfR; subst.
    repeat split...
    apply wf_typ_open_capt with (S := D # Q)...
    destruct (typing_var_implies_binds _ _ _ Typ2) as [C1' [R1' xBinds]].
    apply (wf_cse_term_fvar (C1' # R1') _ _).
    exact xBinds.
  - Case "typing_let".
    repeat split...
    + pick fresh x and apply expr_let...
      assert (x ∉ L) by fsetdec...
      rename select (forall x, _ -> _ ⊢ _ : _) into Typ2.
      rename select (forall x, _ -> _ /\ _ /\ _) into IH.
      unshelve epose proof (Typ2 x _) as Typ2x...
      apply IH...
    + pick fresh x.
      rename select (forall x, _ -> _ /\ _ /\ _) into IH.
      destruct (IH x ltac:(fsetdec)) as [_ [_ WfT2]].
      assert (Γ ⊢ T2 wf).
      { rewrite_env (∅ ++ Γ).
        eapply wf_typ_strengthen with (x := x) (U := C1 # T1)...
      }
      assumption.
  - Case "typing_tabs".
    pick fresh Y; assert (Y ∉ L) by fsetdec...
    rename select (forall x, _ -> _ /\ _ /\ _) into IH.
    unshelve epose proof (IH Y _) as IHY...
    inversion IHY as [Henv [Hexpr Hwf]]...
    repeat split...
    + inversion Henv...
    + pick fresh X and apply expr_tabs...
      destruct (IH X)...
    + constructor...
      eapply typing_cv with (e := (exp_tabs V e1)) (C := exp_cv e1) (R := ∀ [V] T1)...
      * apply typing_tabs with (L := L)...
      * eapply wf_typ_all; trivial.
        apply IH.
      * apply type_from_wf_typ in H.
        pick fresh X and apply type_all...
        eapply type_from_wf_typ with (Γ := [(X, bind_sub V)] ++ Γ).
        apply IH.
        fsetdec.
  - Case "typing_tapp".
    destruct IHTyp as [HwfΓ [Hexpr Hwf]]...
    rename select (_ ⊢ _ <: _) into Sub.
    forwards (R1 & R2 & R3): sub_regular Sub...
    assert (PureQ : pure_type Q).
    { enough (PureQT : pure_type (∀ [Q] T)) by (inversion PureQT; assumption).
      enough (TypeCQT : type (C # ∀ [Q] T)) by (inversion TypeCQT; subst; [ inversion H | assumption ]).
      eapply type_from_wf_typ, Hwf.
    }
    assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ Sub) PureQ)).
    repeat split...
    apply wf_typ_open_type with (R := Q); inversion Hwf; subst...
  - Case "typing_box".
    repeat split...
    apply wf_typ_cse...
    apply type_box.
    eapply type_from_wf_typ.
    applys IHTyp.
  - Case "typing_unbox".
    destruct IHTyp as [HwfΓ [Hex Hwf]].
    inversion Hwf; rename select (_ ⊢ (_ # _) wf) into WfEbCR;
    inversion WfEbCR; rename select (_ ⊢ (□ C # R) wf) into WfbCR;
    inversion WfbCR; subst.
    repeat split...
    apply expr_unbox.
    eapply cset_from_wf_cset...
    eassumption.
  - Case "typing_sub".
    destruct IHTyp as [HwfΓ [Hex Hwf]].
    repeat split...
    eapply sub_regular; eassumption.
Qed.

Lemma eval_typing_regular : forall Γ K T U,
  Γ ⊢ K : T ⇒ U ->
  Γ ⊢ wf /\ Γ ⊢ T wf /\ Γ ⊢ U wf.
Proof with eauto*.
  intros * EvalTyp.
  induction EvalTyp.
  - rename select (_ ⊢ _ <: _) into Sub.
    destructs sub_regular Sub.
    repeat split...
  - pick fresh x and specialize H.
    destructs typing_regular H as [wf_xTE _].
    inversion wf_xTE; subst...
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [ok_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [ok] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_cse ?E ?C) =>
  match goal with
  | H: subcset _ C _ |- _ => apply (proj1 (subcapt_regular _ _ _ H))
  | H: subcset _ _ C |- _ => apply (proj2 (subcapt_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ _ H))
  end
: core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end
: core.

Hint Extern 1 (type ?T) =>
  let go E := eapply (type_from_wf_typ E); eauto in
  match goal with
  | H: typing ?E _ _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  | H: wf_typ ?E _ _ T |- _ => go E
  end
: core.

Hint Extern 1 (cset ?C) =>
  let go E := eapply (cset_from_wf_cset E); eauto in
  match goal with
  | H: subcset ?E C _ |- _ => go E
  | H: subcset ?E _ C |- _ => go E
  | H: exp_cv ?E _ C |- _ => go E
  end
: core.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ H)))
  end
: core.

(** * #<a name="auto"></a># Automation Tests *)

Local Lemma test_subcset_regular : forall Γ C1 C2,
  Γ ⊢ₛ C1 <: C2 ->
  Γ ⊢ₛ C1 wf /\ Γ ⊢ₛ C2 wf.
Proof with eauto*.
  intros.
  repeat split.
  all: auto.
Qed.

Lemma map_subst_cb_id : forall G x C,
  wf_env G ->
  x `notin` dom G ->
  G = map (subst_cb x C) G.
Proof with eauto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_ct_fresh... assert (Z ∉ (fv_tt T) `u`A (fv_ct T)).
    { eapply notin_fv_wf_typ. apply H0. fsetdec. }
    fsetdec.
  rewrite <- IHwf_env...
    assert ([(x, bind_typ (C # R))] = [(x, bind_typ (subst_cse Z P C # subst_ct Z P R))]).
    { f_equal. f_equal. f_equal. f_equal.
      - rewrite <- subst_cse_fresh... apply (notin_fv_wf_typ Γ Z) in H0. simpl in H0.
        fsetdec. fsetdec.
      - rewrite <- subst_ct_fresh... apply (notin_fv_wf_typ Γ Z) in H0. simpl in H0.
        fsetdec. fsetdec. }
    rewrite H2...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf_typ; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf_typ with (Γ:=Γ); eauto.
  inversion H0...
Qed.


Lemma subcapt_regular' : forall Γ C D,
  Γ ⊢ₛ C <: D ->
  wf_env Γ /\ Γ ⊢ₛ C wf /\ Γ ⊢ₛ D wf.
Proof with eauto*.
  intros * SubCapt.
  dependent induction SubCapt; subst...
Qed.
