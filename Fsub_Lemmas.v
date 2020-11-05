(** Administrative lemmas for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\u00e9raud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of administrative lemmas that we
    require for proving type-safety.  The lemmas mainly concern the
    relations [wf_typ] and [wf_env].

    This file also contains regularity lemmas, which show that various
    relations hold only for locally closed terms.  In addition to
    being necessary to complete the proof of type-safety, these lemmas
    help demonstrate that our definitions are correct; they would be
    worth proving even if they are unneeded for any "real" proofs.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export Fsub_Infrastructure.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(*
(** This is really a sanity check and should be easy to prove. *)
Local Lemma wf_typ_implies_classic : forall E T,
  wf_typ E T -> wf_bound_typ E T.
Proof with eauto; try constructor; eauto.
  (* This is not the way to solve this, as we need to account for the binding
      that is introduced in typ_var and is used in typ_capt.

      A stronger induction hypothesis is needed here.  Maybe wf_covariant_type E Ep Em ->
      wf_bound_typ (E ++ Ep ++ Em), but then there are ordering issues in the environment that
      are really messy to deal with. *)
  intros E T H; induction H...
  - apply wf_bound_typ_var with (U := U)...
  - pick fresh Y and apply wf_bound_typ_arrow...
    admit.
  - pick fresh Y and apply wf_bound_typ_all...
  - admit.
Admitted.
*)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_typ : forall E m T,
  wf_typ E m T -> type T.
Proof with eauto.
  intros E m T H; induction H...
  destruct H0...
Qed.

(* Lemma type_from_wf_covariant_typ : forall E Ep Em T, *)
(*   wf_covariant_typ E Ep Em T -> type T. *)
(* Proof with eauto. *)
(*   intros E Ep Em T H; induction H... *)
(*   destruct H0... *)
(* Qed. *)

(** This is a useful helper tactic for clearing away
    capture set wellformedness. *)

Ltac wf_cset_simpl instantiate_ext :=
  match goal with 
  | H : _ |- (wf_cset _ _ cset_universal) =>
    constructor
  | H : (wf_cset _ _ ?C) |- (wf_cset _ _ ?C) =>
    let Hdestruct := fresh "Hdestruct" in
    let x  := fresh "x" in
    let Hx := fresh "Hxin" in
    let Hexists := fresh "Hexists" in
    let T := fresh "T" in
    let Hbound := fresh "Hbound" in
    let tmp1 := fresh "tmp1" in
    let tmp2 := fresh "tmp2" in
    let fvars := fresh "fvars" in
    let tmp3 := fresh "tmp3" in
      inversion H as [|tmp1 tmp2 fvars Hbound tmp3]; subst; [ auto | 
        constructor;
        unfold allbound_typ in Hbound;
        intros x Hx;
        destruct (Hbound x Hx) as [T Hexists];
        lazymatch instantiate_ext with
        | True => exists T; destruct Hexists
        | False => idtac
      end ]
  end.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

(** These two lemmas give a general weakening lemma for wf_covariant_typ.
    They stay separate as the techniques needed to prove them are different. *)
(* Local Lemma wf_covariant_typ_weakening_env : forall T E F G Ep Em, *)
(*   wf_covariant_typ (G ++ E) Ep Em T -> *)
(*   ok (G ++ F ++ E) -> *)
(*   wf_covariant_typ (G ++ F ++ E) Ep Em T. *)
(* Proof with simpl_env; eauto; try fsetdec. *)
(*   intros T E F G Ep Em Hwf_typ Hk. *)
(*   remember (G ++ E). *)
(*   generalize dependent G. *)
(*   induction Hwf_typ; intros G Hok Heq; subst; auto. *)
(*   - apply wf_typ_var with (U := U)... *)
(*   - pick fresh Y and apply wf_typ_arrow... *)
(*   - pick fresh Y and apply wf_typ_all... *)
(*     apply H0 with (X := Y) (G0 := [(Y, bind_sub T1)] ++ G)... *)
(*   - apply wf_typ_capt... *)
(*     wf_cset_simpl True... *)
(* Qed. *)
(* Local Lemma wf_covariant_typ_weakening_variance : forall T E Ep Gp Fp Em Gm Fm, *)
(*   wf_covariant_typ E (Gp ++ Ep) (Gm ++ Em) T -> *)
(*   ok (Gp ++ Fp ++ Ep) \/ Fp = empty -> *)
(*   ok (Gm ++ Fm ++ Em) \/ Fm = empty -> *)
(*   wf_covariant_typ E (Gp ++ Fp ++ Ep) (Gm ++ Fm ++ Em) T. *)
(* Proof with simpl_env; auto. *)
(*   intros T E Ep Gp Fp Em Gm Fm Hwf_typ Hokp Hokm. *)
(*   remember (Gp ++ Ep). *)
(*   remember (Gm ++ Em). *)
(*   generalize dependent Gp. *)
(*   generalize dependent Gm. *)
(*   generalize dependent Fp. *)
(*   generalize dependent Fm. *)
(*   generalize dependent Ep. *)
(*   generalize dependent Em. *)
(*   induction Hwf_typ; intros Em' Ep' Fm Fp Gm Heqm Hokm Gp Heqp Hokp; subst; auto. *)
(*   - apply wf_typ_var with (U := U)... *)
(*   - pick fresh Y and apply wf_typ_arrow... *)
(*     apply H0 with (Gp0 := [(Y, bind_typ T1)] ++ Gp)... *)
(*     inversion Hokp. *)
(*     + left... *)
(*     + right... *)
(*   - pick fresh Y and apply wf_typ_all... *)
(*   - apply wf_typ_capt... *)
(*     wf_cset_simpl True... *)
(*     + right. destruct Hokp; subst... *)
(* Qed. *)

(** This is the proper well-formedness lemma that we expose, wrapping up the two
    helper lemmas. *)
(* Lemma wf_covariant_typ_weakening : forall T E G F Ep Gp Fp Em Gm Fm, *)
(*   wf_covariant_typ (G ++ E) (Gp ++ Ep) (Gm ++ Em) T -> *)
(*   ok (G ++ F ++ E) \/ F = empty -> *)
(*   ok (Gp ++ Fp ++ Ep) \/ Fp = empty -> *)
(*   ok (Gm ++ Fm ++ Em) \/ Fm = empty -> *)
(*   wf_covariant_typ (G ++ F ++ E) (Gp ++ Fp ++ Ep) (Gm ++ Fm ++ Em) T. *)
(* Proof with auto. *)
(*   intros. *)
(*   inversion H0. *)
(*   + apply wf_covariant_typ_weakening_env... *)
(*     apply wf_covariant_typ_weakening_variance... *)
(*   + apply wf_covariant_typ_weakening_variance... *)
(*     assert (G ++ F ++ E = G ++ E). { *)
(*       subst. simpl_env. auto. *)
(*     } *)
(*     subst. auto. *)
(* Qed. *)
(** A simplification for just weakening wf_typ, which is used fairly often. *)

Lemma wf_cset_weakening : forall E F G Ep C,
    wf_cset (G ++ E) Ep C ->
    ok (G ++ F ++ E) ->
    wf_cset (G ++ F ++ E) Ep C.
Proof with auto*.
  intros E F G Ep C Hcset Henv.
  remember (G ++ E).
  induction Hcset ; subst...
  (* Only complicated case is dealing with wf_cset. *)
  apply wf_concrete_cset.
  unfold allbound_typ in *.
  intros x Hb.
  specialize (H x Hb).
  destruct H as [ T [ p [ H1 H2 ] ] ] ; eauto using binds_weaken.
Qed.

Lemma wf_typ_weakening : forall T E m F G,
  wf_typ (G ++ E) m T ->
  ok (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) m T.
Proof with simpl_env; auto.
  intros.
  remember (G ++ E).
  generalize dependent G.
  induction H; intros G Heql Hok; subst...
  - apply wf_typ_var with (U := U)...
  - pick fresh Y and apply wf_typ_arrow...
    assert (Y `notin` L) as P by fsetdec.
    apply (H1 Y P ([(Y, bind_typ T1 (polarity_from_mode (neg m)))] ++ G))...
  - pick fresh Y and apply wf_typ_all...
    assert (Y `notin` L) as P by fsetdec.
    apply (H1 Y P ([(Y, bind_sub T1)] ++ G))...
  - apply wf_typ_capt...
    apply wf_cset_weakening...
Qed.

(** Two simplifications for trimming off the head of the environment. *)
(* Lemma wf_covariant_typ_weaken_head : forall T E Ep Em F, *)
(*   wf_covariant_typ E Ep Em T -> *)
(*   ok (F ++ E) -> *)
(*   wf_covariant_typ (F ++ E) Ep Em T. *)
(* Proof with auto. *)
(*   intros. *)
(*   rewrite_env (empty ++ F ++ E). *)
(*   rewrite_env (empty ++ empty ++ Ep). *)
(*   rewrite_env (empty ++ empty ++ Em). *)
(*   apply wf_covariant_typ_weakening; simpl_env... *)
(* Qed. *)

Lemma wf_typ_weaken_head : forall T E m F,
  wf_typ E m T ->
  ok (F ++ E) ->
  wf_typ (F ++ E) m T.
Proof.
  intros.
  rewrite_env (empty ++ F ++ E).
  auto using wf_typ_weakening.
Qed.

(** Narrowing for wellformedness. *)
(* Lemma wf_covariant_typ_narrowing : forall V U T E F X Ep Em, *)
(*   wf_covariant_typ (F ++ [(X, bind_sub V)] ++ E) T Ep Em-> *)
(*   ok (F ++ [(X, bind_sub U)] ++ E) -> *)
(*   wf_covariant_typ (F ++ [(X, bind_sub U)] ++ E) T Ep Em. *)
(* Proof with simpl_env; eauto. *)
(*   intros V U T E F X Ep Em Hwf_typ Hok. *)
(*   remember (F ++ [(X, bind_sub V)] ++ E). *)
(*   generalize dependent F. *)
(*   induction Hwf_typ; intros F Hok Heq; subst; auto. *)
(*   (* typ_var *) *)
(*   - binds_cases H... *)
(*   (* typ_arrow *) *)
(*   - pick fresh Y and apply wf_typ_arrow... *)
(*   (* typ_all *) *)
(*   - pick fresh Y and apply wf_typ_all... *)
(*     rewrite <- concat_assoc. *)
(*     apply H0... *)
(*   (* typ_capt *) *)
(*   - eapply wf_typ_capt... *)
(*     wf_cset_simpl True... *)
(*     + binds_cases H0... *)
(* Qed. *)

(** Again, a simpler version which is used more often. *)
Lemma wf_typ_narrowing : forall V U T E m F X,
  wf_typ (F ++ [(X, bind_sub V)] ++ E) m T ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_typ (F ++ [(X, bind_sub U)] ++ E) m T.
Proof with simpl_env; eauto.
  intros.
  remember (F ++ [(X, bind_sub V)] ++ E).
  generalize dependent F.
  induction H; intros F Hok Heq; subst; auto.
  (* typ_var *)
  - binds_cases H...
  (* typ_arrow *)
  - pick fresh Y and apply wf_typ_arrow...
    apply H1 with (X0 := Y) (F0 := [(Y, bind_typ T1 (polarity_from_mode (neg m)))] ++ F)...
  (* typ_all *)
  - pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H1 with (X0 := Y) (F0 := [(Y, bind_sub T1)] ++ F)...
  (* typ_capt *)
  - eapply wf_typ_capt...
    wf_cset_simpl True...
    inversion H1.
    binds_cases H3...
Qed.

(** Lemmas around substituion, and how they preserve local closure.
    We need a technical lemma around substituting in the presence of +/-
    variance sets. *)
(* Local Lemma wf_covariant_typ_subst_tb : forall F Fp Fm Q E Ep Em Z P T, *)
(*   wf_covariant_typ (F ++ [(Z, bind_sub Q)] ++ E) (Fp ++ Ep) (Fm ++ Em) T -> *)
(*   wf_typ E P -> *)
(*   ok (map (subst_tb Z P) F ++ E) -> *)
(*   ok (map (subst_tb Z P) Fp ++ Ep) -> *)
(*   ok (map (subst_tb Z P) Fm ++ Em) -> *)
(*   wf_covariant_typ (map (subst_tb Z P) F ++ E) (map (subst_tb Z P) Fp ++ Ep) (map (subst_tb Z P) Fm ++ Em) (subst_tt Z P T). *)
(* Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ. *)
(*   intros F Fp Fm Q E Ep Em Z P T WT WP. *)
(*   remember (F ++ [(Z, bind_sub Q)] ++ E). *)
(*   remember (Fp ++ Ep). *)
(*   remember (Fm ++ Em). *)
(*   generalize dependent F. *)
(*   generalize dependent Fp. *)
(*   generalize dependent Fm. *)
(*   generalize dependent Ep. *)
(*   generalize dependent Em. *)
(*   induction WT; intros Em' Ep' Fm EQm Fp EQp F EQ Ok OkP OkM; subst; simpl subst_tt... *)
(*   - Case "wf_typ_var". *)
(*     destruct (X == Z); subst... *)
(*     + SCase "X = Z". *)
(*       binds_cases H... *)
(*       all: rewrite_env (empty ++ map (subst_tb Z P) F ++ E); *)
(*            rewrite_env (empty ++ ((map (subst_tb Z P) Fp) ++ Ep') ++ empty); *)
(*            rewrite_env (empty ++ ((map (subst_tb Z P) Fm) ++ Em') ++ empty); *)
(*            apply wf_covariant_typ_weakening... *)
(*     + SCase "X <> Z". *)
(*       binds_cases H... *)
(*       apply (wf_typ_var (subst_tt Z P U))... *)
(*   - Case "wf_typ_arrow". *)
(*     pick fresh Y and apply wf_typ_arrow... *)
(*     unfold open_ct. *)
(*     rewrite <- subst_tt_open_ct_rec. *)
(*     apply H0 with (F0 := F) (Fp0 := [(Y, bind_typ T1)] ++ Fp) (Fm0 := Fm) (Em := Em') (Ep := Ep') (X := Y)... *)
(*     apply type_from_wf_typ with (E := E)... *)
(*   - Case "wf_typ_var". *)
(*     pick fresh Y and apply wf_typ_all... *)
(*     rewrite subst_tt_open_tt_var... *)
(*     rewrite_env (map (subst_tb Z P) ([(Y, bind_sub T1)] ++ F) ++ E). *)
(*     apply H0... *)
(*   - Case "wf_typ_capt". *)
(*     apply wf_typ_capt... *)
(*     (** Here we need to do the manual destruction of the binding term, as the type x is bound to *)
(*         might need to be substituted in. *) *)
(*     wf_cset_simpl False. *)
(*     destruct Hexists; binds_cases H0; eauto; exists (subst_tt Z P T0)... *)
(* Qed. *)

Lemma double_negation : forall m, (neg (neg m)) = m.
Proof with auto.
  intros.
  unfold neg. destruct m...
Qed.
Hint Rewrite double_negation : core.

Lemma wf_typ_subst_tb : forall F Q E m Z P T,
  wf_typ (F ++ [(Z, bind_sub Q)] ++ E) m T ->
  (** NOTE here that P needs to be well formed in both the + and - environments,
      as we're substituting in both places. *)
  wf_typ E m P ->
  wf_typ E (neg m) P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) m (subst_tt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E m Z P T HwfT HwfPp HwfPm Hok.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  remember m.
  generalize dependent F.
  generalize dependent m.
  induction HwfT; intros m' EQm' F EQF Hok; subst; simpl subst_tt...
  - Case "wf_typ_var".
    destruct (X == Z); subst...
    + SCase "X <> Z".
      binds_cases H...
      apply (wf_typ_var (subst_tt Z P U))...
  - Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    + SCase "T1".
      apply IHHwfT with (m := neg m')...
      autorewrite with core...
    + SCase "T2".
      unfold open_ct in *...
      rewrite <- subst_tt_open_ct_rec...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_typ T1 (polarity_from_mode (neg m')))] ++ F) ++ E).
      apply H0 with (m := m')...
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    + SCase "T1".
      apply IHHwfT with (m := neg m')...
      autorewrite with core...
    + SCase "T2".
      unfold open_ct in *...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub T1)] ++ F) ++ E).
      apply H0 with (m := m')...
  - Case "wf_typ_capt".
    apply wf_typ_capt...
    wf_cset_simpl False.
    destruct Hexists as [p [Hcapture Hbinds]];
      binds_cases Hbinds;
      eauto*;
      exists (subst_tt Z P T0);
      exists p...
    split...
    rewrite_env (map (subst_tb Z P) F ++ E ++ empty)...
    apply binds_map with (f := subst_tb Z P) in H1...
Qed.

Lemma wf_typ_open : forall E m U T1 T2,
  ok E ->
  wf_typ E m (typ_all T1 T2) ->
  wf_typ E m U ->
  wf_typ E (neg m) U ->
  wf_typ E m (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E m U T1 T2 O WA WUp WUm.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  apply wf_typ_subst_tb with (Q := T1)...
Qed.

(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma ok_from_wf_env : forall E,
  wf_env E ->
  ok E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [ok_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [ok_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve ok_from_wf_env : core.

Lemma wf_typ_from_binds_typ : forall x U E m,
  wf_env E ->
  binds x (bind_typ U (polarity_from_mode m)) E ->
  wf_typ E m U.
Proof with eauto using wf_typ_weaken_head.
  intros x U E m Hwf Hbinds.
  (* remember m; generalize dependent m. *)
  induction Hwf; binds_cases Hbinds...
  inversion H3; subst...
  (** This probably needs m = m0 here *)
Admitted.

Lemma wf_typ_from_wf_env_typ : forall x T E m,
  wf_env ([(x, bind_typ T (polarity_from_mode m))] ++ E) ->
  wf_typ E m T.
Proof.
  intros x T E m H. inversion H; auto.
  (** This probably needs m = m0 here *)
Admitted.

Lemma wf_typ_from_wf_env_sub : forall x T E m,
  wf_env ([(x, bind_sub T)] ++ E) ->
  wf_typ E m T.
Proof.
  intros x T E m H. inversion H; auto.
  (** This probably needs m = m0 here *)
Admitted.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ [(X, bind_sub V)] ++ E) ->
  wf_typ E U ->
  wf_env (F ++ [(X, bind_sub U)] ++ E).
Proof with eauto 6 using wf_typ_narrowing.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.


Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
Qed.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

(** These proofs are all the same, but Coq isn't smart enough unfortunately... *)
Local Lemma notin_fv_tt_open_tt : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.
Local Lemma notin_fv_tt_open_et : forall (Y X : atom) T,
  X `notin` fv_et (open_tt T Y) ->
  X `notin` fv_et T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.
Local Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_et (open_tt T Y) ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with auto.
 intros. apply notin_union.
 - apply notin_fv_tt_open_tt with (Y := Y)...
 - apply notin_fv_tt_open_et with (Y := Y)...
Qed.

(** Again, these proofs are all the same, but Coq isn't smart enough unfortunately. *)
Local Lemma notin_fv_ct_open_tt : forall (X : atom) T C,
  X `notin` fv_tt (open_ct T C) ->
  X `notin` fv_tt T.
Proof with auto.
  intros X T C. unfold open_ct.
  generalize 0.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 k)...
  - specialize (IHT1 k). specialize (IHT2 k)...
Qed.
Local Lemma notin_fv_ct_open_et : forall (X : atom) T C,
  C <> cset_universal ->
  X `notin` fv_et (open_ct T C) ->
  X `notin` fv_et T.
Proof with auto.
  intros X T C Hc. unfold open_ct.
  generalize 0.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 k)...
  - specialize (IHT1 k). specialize (IHT2 k)...
  - notin_simpl. clear IHT H0.
    revert H. unfold cset_fvar. unfold open_captureset_bvar. cset_split; destruct C eqn:HC; destruct c eqn:Hcd...
  - specialize (IHT k)...
Qed.
Lemma notin_fv_ct_open : forall (X : atom) T C,
  C <> cset_universal ->
  X `notin` fv_et (open_ct T C) ->
  X `notin` fv_tt (open_ct T C) ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with auto.
  intros. apply notin_union...
  - apply notin_fv_ct_open_tt with (C := C)...
  - apply notin_fv_ct_open_et with (C := C)...
Qed.

(* Maybe we need to generalize this to E Ep and Em.
   Hopefully not.... *)
Lemma notin_fv_wf_covariant : forall E Ep Em (X : atom) T,
  wf_covariant_typ E Ep Em T ->
  X `notin` dom E ->
  X `notin` dom Ep ->
  X `notin` dom Em ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with eauto.
  intros E Ep Em X T Wf_typ.
  induction Wf_typ; intros FrE FrEp FrEm; simpl.
  - fsetdec.
  - assert (X0 `in` dom E) by (eapply binds_In; eauto)...
  - pick fresh Y.
    assert (Y `notin` L) by fsetdec.
    assert (X `notin` dom ([(Y, bind_typ T1)] ++ Ep)). {
      simpl_env. fsetdec.
    }
    specialize (H0 Y H1 FrE H2 FrEm).
    notin_simpl.
    repeat apply notin_union...
    + apply notin_fv_ct_open_tt with (C := cset_singleton_fvar Y)...
    + apply notin_fv_ct_open_et with (C := cset_singleton_fvar Y).
      discriminate. intuition.
  - pick fresh Y.
    assert (Y `notin` L) by fsetdec.
    assert (X `notin` dom ([(Y, bind_typ T1)] ++ E)). {
      simpl_env. fsetdec.
    }
    specialize (H0 Y H1 H2 FrEp FrEm).
    notin_simpl.
    repeat apply notin_union...
    + apply notin_fv_tt_open_tt with (Y := Y)...
    + apply notin_fv_tt_open_et with (Y := Y)...
  - specialize (IHWf_typ FrE FrEp FrEm).
    inversion H;
    destruct C.
    + fsetdec.
    + repeat apply notin_union; try fsetdec.
    + contradict H3; discriminate.
    + repeat apply notin_union; try fsetdec.
      unfold cset_fvars in *.
      unfold allbound_typ in *.
      unfold cset_fvar.
      intro.
      specialize (H0 X H4).
      destruct H0.
      destruct H0.
      * assert (X `in` dom E) by (eapply binds_In; eauto).
        contradiction.
      * assert (X `in` dom Ep) by (eapply binds_In; eauto).
        contradiction.
Qed.
Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with eauto.
  intros E X T Wf_typ F.
  assert (X `notin` (fv_tt T `union` fv_et T)). {
    eapply notin_fv_wf_covariant...
  }
  fsetdec.
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.

(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma subcapt_regular : forall E C1 C2,
  subcapt E C1 C2 ->
  wf_cset E empty C1 /\ wf_cset E empty C2.
Proof with eauto*.
  intros. inversion H...
Qed.

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E S T H.
  induction H...
  - Case "sub_top".
    repeat split... constructor.
  - Case "sub_trans_tvar".
    repeat split...
    apply wf_typ_var with (U := U)...
  - Case "sub_capt".
    pose proof (subcapt_regular E C1 C2)...
    repeat split; try constructor...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E e T H; induction H...
  - repeat split...
    constructor...
    + apply wf_typ_from_binds_typ with (x := x)...
    + constructor...
      unfold allbound_typ. intros. assert (x0 = x) by fsetdec. subst; eauto.
  - pick fresh X; assert (X `notin` L) by fsetdec...
    specialize (H0 X H3) as H4; inversion H4...
    repeat split...
    + inversion H5...
    + econstructor...
      * apply type_from_wf_typ with (E := E).
        apply wf_typ_from_wf_env_typ with (x := X)...
      * instantiate (1 := L). intros...
        specialize (H0 x H7) as H8...
  - pick fresh X. assert (X `notin` L) by fsetdec...
    specialize (H0 X H3) as H4; inversion H4...
    repeat split...
    + inversion H5...
    + econstructor...
      * apply type_from_wf_typ with (E := E).
        apply wf_typ_from_wf_env_sub with (x := X)...
      * instantiate (1 := L). intros...
        specialize (H0 X0 H7) as H8...
  - repeat split...
    constructor...
    pose proof (sub_regular E T T1 H0).
    apply type_from_wf_typ with (E := E)...
  - repeat split...
    pose proof (sub_regular E S T H0)...
Qed.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma cv_free_is_bvar_free : forall e C,
  cv_free e C ->
  empty_cset_bvars C.
Proof with eauto*.
  intros. induction H... 
  - simpl; fnsetdec...
  - simpl; fnsetdec...
  - destruct C1; destruct C2...
    csethyp. unfold empty_cset_bvars in *. unfold cset_bvars in *.
    fnsetdec.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with auto*.
  intros e e' H.
  induction H; assert(J := value_regular); split...
  - Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y)...
    apply subst_ee_expr...
    apply cv_free_is_bvar_free with (e := v2)...
  - Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
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

Hint Extern 1 (wf_cset ?E ?m) =>
  match goal with
  | H: subcapt _ _ _ _ |- _ => apply (proj1 (subcapt_regular _ _ _ _ H))
  end
: core.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: (forall m0, sub _ m0 _ _) |- _ => apply (proj1 (sub_regular _ _ _ _ (H covariant)))
  | H: sub _ _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_typ ?E ?m ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E m T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ _ H)))
  | H: sub E m _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ _ H)))
  | H: (forall m0, sub E m0 T _) |- _ => apply (proj1 (proj2 (sub_regular _ _ _ _ (H m))))
  | H: (forall m0, sub E m0 _ T) |- _ => apply (proj2 (proj2 (sub_regular _ _ _ _ (H m))))
  end
: core.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E _ T _ |- _ => go E
  | H: sub ?E _ _ T |- _ => go E
  | H: wf_typ ?E T |- _ => go E
  end
: core.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end
: core.
