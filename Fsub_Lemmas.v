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

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof with eauto.
  intros E T H; induction H...
  destruct H0...
Qed.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_covariant_typ_weakening : forall T E F G Ep Em,
  wf_covariant_typ (G ++ E) Ep Em T ->
  ok (G ++ F ++ E) ->
  wf_covariant_typ (G ++ F ++ E) Ep Em T.
Proof with simpl_env; eauto; try fsetdec.
  intros T E F G Ep Em Hwf_typ Hk.
  remember (G ++ E).
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst; auto.
  - assert (binds X (bind_sub U) (G ++ F ++ E)).
    + apply binds_weaken; trivial.
    + apply wf_typ_var with (U := U); trivial.
  - pick fresh Y and apply wf_typ_arrow.
    apply IHHwf_typ...
    apply H0 with (G0 := G)...
  - pick fresh Y and apply wf_typ_all.
    apply IHHwf_typ...
    apply H0 with (X := Y) (G0 := [(Y, bind_sub T1)] ++ G)...
  - apply wf_typ_capt.
    apply IHHwf_typ...
    unfold wf_cset in *.
    split.
    + apply H.
    + unfold allbound in *.
      csetdec.
      destruct C...
      inversion H.
      simpl_env in *.
      fsetdec.
Qed.

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof.
  eauto using wf_covariant_typ_weakening.
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  ok (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_covariant_typ_narrowing : forall V U T E F X Ep Em,
  wf_covariant_typ (F ++ [(X, bind_sub V)] ++ E) T Ep Em->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_covariant_typ (F ++ [(X, bind_sub U)] ++ E) T Ep Em.
Proof with simpl_env; eauto.
  intros V U T E F X Ep Em Hwf_typ Hok.
  remember (F ++ [(X, bind_sub V)] ++ E).
  generalize dependent F.
  induction Hwf_typ; intros F Hok Heq; subst; auto.
  (* typ_var *)
  - binds_cases H...
  (* typ_arrow *)
  - pick fresh Y and apply wf_typ_arrow...
  (* typ_all *)
  - pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
  (* typ_capt *)
  - eapply wf_typ_capt...
    unfold wf_cset in *.
    split...
    + csetdec; destruct C; csetdec... apply H.
    + csetdec; destruct C... apply H. simpl_env in *. unfold allbound in *. fsetdec.
Qed.

Lemma wf_typ_narrowing : forall V U T E F X,
  wf_typ (F ++ [(X, bind_sub V)] ++ E) T ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_typ (F ++ [(X, bind_sub U)] ++ E) T.
Proof with simpl_env; eauto.
  eauto using wf_covariant_typ_narrowing.
Qed.

(* X could occur in a capture set in T 
   TODO maybe modify the lemma to include 
    X `notin` fv_et T
*)
Lemma wf_covariant_typ_strengthening : forall E F G1 G2 X U T,
 wf_covariant_typ (F ++ [(X, bind_typ U)] ++ E) G1 G2 T ->
 wf_covariant_typ (F ++ E) G1 G2 T.
Proof.
  intros E F G1 G2 X U T H.
  remember (F ++ [(X, bind_typ U)] ++ E).
  remember G1.
  remember G2.
  generalize dependent F.
  generalize dependent G1.
  generalize dependent G2.
  induction H ; intros G2 Heqm G1 Heqp F Heq ; subst; auto.
  - binds_cases H ; eauto.
  - eapply wf_typ_arrow with (L := L); eauto.
  - pick fresh Y and apply wf_typ_all; eauto.
    rewrite <- concat_assoc.
    eapply H1; auto.
  - apply wf_typ_capt.
    + apply IHwf_covariant_typ with (G3 := G2) (G4 := G1) ; auto.
    + destruct H0. econstructor ; auto. 
      unfold allbound in *. 
      csetdec.
      destruct C.
      apply H1.
      simpl_env in *.
      assert (X `notin` t). { admit. }
      fsetdec.
Admitted.

Lemma wf_typ_strengthening : forall E F X U T,
 wf_typ (F ++ [(X, bind_typ U)] ++ E) T ->
 wf_typ (F ++ E) T.
Proof.
  eauto using wf_covariant_typ_strengthening.
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T,
  wf_typ (F ++ [(Z, bind_sub Q)] ++ E) T ->
  wf_typ E P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T WT WP.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X <> Z".
      binds_cases H...
      apply (wf_typ_var (subst_tt Z P U))...
      simpl_env in *.
      unfold binds.
      
      admit.
      admit.
  Case "wf_typ_arrow".
    admit.
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    admit.
    admit.
  Case "wf_typ_capt".
    admit.
    (* rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub T1)] ++ F) ++ E).
    apply H0... *)
Admitted.

Lemma wf_typ_open : forall E U T1 T2,
  ok E ->
  wf_typ E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  eapply wf_typ_subst_tb...
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

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; binds_cases J...
  inversion H4; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_typ T)] ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env ([(x, bind_sub T)] ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


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

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ [(x, bind_typ T)] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
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

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_ct_open : forall (X : atom) T C,
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

(* Maybe we need to generalize this to E Ep and Em? *)
Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl ; try apply notin_union...
  - assert (X0 `in` (dom E))...
    eapply binds_In; eauto.
  - pick fresh Y.
    specialize (IHWf_typ Fr).
    assert (Y `notin` L). { fsetdec. }
    specialize (H0 Y H1 Fr). 
    apply notin_fv_ct_open with (C := (cset_singleton_fvar Y))...
  - pick fresh Y.
    specialize (IHWf_typ Fr).
    assert (Y `notin` L). { fsetdec. }
    specialize (H0 Y H1).
    apply notin_fv_tt_open with (Y := Y)...
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

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E S T H.
  induction H...
  Case "sub_trans_tvar".
    eauto*.
  Case "sub_arrow".
    destruct IHsub.
    destruct H3.
    repeat split ; auto.
    pick fresh Y and apply wf_typ_arrow...
    destruct (H1 Y) as [HEnv [HS2 HT2]]...
    admit.
    econstructor...
    intros.
    admit.
  Case "sub_all".
    destruct IHsub ; auto.
    destruct H3.
    repeat split ; auto.
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
      destruct H6...
      rewrite_env (empty ++ [(Y, bind_sub S1)] ++ E).
      apply (wf_typ_narrowing T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
  (* Do we need to add wf conditions on capturesets to subcapt just for regularity?  *)
  Case "sub_capt".
    destruct IHsub ; auto.
    destruct H2.
    repeat split ; auto.
    SCase "Second of original three conjuncts".
      - constructor ; auto.
        unfold wf_cset.
        admit.
      - constructor ; auto.
        admit.
Admitted.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E e T H; induction H...
  Case "typing_var".
    repeat split...
    apply wf_typ_from_binds_typ with (x := x) ; auto.
    admit.
  Case "typing_abs".
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. inversion Hok...
    SCase "Second of original three conjuncts".
      pick fresh x and apply expr_abs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
        destruct (H0 x)...
    SCase "Third of original three conjuncts".
      apply wf_typ_capt.
      apply wf_typ_arrow with (L := L).
      apply wf_typ_from_wf_env_typ with (x := y) ; auto.
      admit.
      admit.
      (* eapply wf_typ_arrow. ; eauto using wf_typ_from_wf_env_typ.
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto. *)      
  Case "typing_app".
    repeat split...
    destruct IHtyping1 as [_ [_ K]].
    inversion K ; admit...
  Case "typing_tabs".
    pick fresh Y.
    destruct (H0 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split.
    auto.
    SCase "Second of original three conjuncts".
      pick fresh X and apply expr_tabs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
        destruct (H0 X)...
    SCase "Third of original three conjuncts".
      pick fresh Z.
      eapply wf_typ_capt.
      destruct (H0 Z)...
      admit.
      admit.
  Case "typing_tapp".
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]].
    repeat split...
    SCase "Second of original three conjuncts".
      apply expr_tapp...
      eauto using type_from_wf_typ.
    SCase "Third of original three conjuncts".
      destruct IHtyping as [R1' [R2' R3']].
      eapply wf_typ_open; eauto.
      admit.
  Case "typing_sub".
    repeat split...
    destruct (sub_regular _ _ _ H0)...
Admitted.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with auto*.
  intros e e' H.
  induction H; assert(J := value_regular); split...
  Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y)...
    (* rewrite <- subst_ee_open_ee_var. *)
    admit.    
  Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
Admitted.


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

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end
: core.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
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
