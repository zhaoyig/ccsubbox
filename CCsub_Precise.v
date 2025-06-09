Require Import Coq.Program.Equality.
Require Import LibTactics.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.
Require Import CCsub_Red.
Require Import CCsub_Inversion.

Inductive prec_typing : ctx -> store_ctx -> exp -> typ -> Prop :=
  | prec_typing_var : forall Γ x S C R,
      wf_ctx Γ S ->
      binds x (bind_typ (C # R)) Γ ->
      prec_typing Γ S x (cse_fvar x # R)
  | prec_typing_abs : forall L Γ C R e1 T1 S,
      wf_typ Γ S (C # R) ->
      (forall x : atom, x ∉ L ->
        prec_typing ([(x, bind_typ (C # R))] ++ Γ) S (open_ve e1 x (cse_fvar x)) (open_ct T1 (cse_fvar x))) ->
      prec_typing Γ S (λ (C # R) e1) (exp_cv e1 # ∀ (C # R) T1)
  | prec_typing_app : forall D Q Γ (f x : atom) T C S,
      prec_typing Γ S f (C # (∀ (D # Q) T)) ->
      prec_typing Γ S x (D # Q) ->
      prec_typing Γ S (f @ x) (open_ct T (exp_cv x))
  | prec_typing_let : forall L C1 R1 T Γ e k S,
      prec_typing Γ S e (C1 # R1) ->
      (forall x : atom, x ∉ L ->
        prec_typing ([(x, bind_typ (C1 # R1))] ++ Γ) S (open_ve k x (cse_fvar x)) T) ->
      prec_typing Γ S (let= e : (C1 # R1) in k) T
  | prec_typing_tabs : forall L Γ V e1 T1 S,
      wf_typ Γ S V ->
      pure_type V ->
      (forall X : atom, X ∉ L ->
        prec_typing ([(X, bind_sub V)] ++ Γ) S (open_te e1 X) (open_tt T1 X)) ->
      prec_typing Γ S (Λ [V] e1) (exp_cv e1 # ∀ [V] T1)
  | prec_typing_tapp : forall Γ (x : atom) P Q T C S,
      prec_typing Γ S x (C # ∀ [Q] T) ->
      sub Γ S P Q ->
      prec_typing Γ S (x @ [P]) (open_tt T P)
  | prec_typing_box : forall Γ S (x : atom) C R,
      prec_typing Γ S x (C # R) ->
      wf_cse Γ S C ->
      prec_typing Γ S (box x) ({} # □ (C # R))
  | prec_typing_unbox : forall Γ S (x : atom) C R,
      prec_typing Γ S x ({} # □ (C # R)) ->
      wf_cse Γ S C ->
      prec_typing Γ S (C ⟜ x) (C # R).

Inductive prec_store_typing : store_env -> store_ctx  -> Prop :=
  | prec_typing_store_nil:
      prec_store_typing nil nil
  | prec_typing_store_cons : forall l C R v Γ SS E S,
      prec_store_typing SS S ->
      value (v, E) ->
      env_well_typed S E Γ ->
      wf_typ nil S (C # R) ->
      prec_typing Γ S v (C # R) ->
      l `Notin` Store.dom S ->
      prec_store_typing ((l, store (v , E)) :: SS) ((l, (C # R)) :: S).

Inductive prec_eval_typing (Γ : ctx) (S : store_ctx) : cont -> typ -> typ -> Prop :=
  | prec_typing_eval_nil : forall C1 R1 C2 R2,
      sub Γ S (C1 # R1) (C2 # R2) ->
      prec_eval_typing Γ S nil (C1 # R1) (C2 # R2)
  | prec_typing_eval_cons : forall L e K C1 R1 C2 R2 C3 R3 E,
      scope e ->
      (forall x, x ∉ L ->
        prec_typing ([(x, bind_typ (C1 # R1))] ++ Γ) S (open_ve e x (cse_fvar x)) (C2 # R2)) ->
      env_well_typed S E Γ ->
      prec_eval_typing Γ S K (C2 # R2) (C3 # R3) ->
      prec_eval_typing Γ S ((let_body (e, E) (C1 # R1)) :: K) (C1 # R1) (C3 # R3).

Inductive prec_state_typing : state -> typ -> Prop :=
  | prec_typing_state : forall Γ Γ' S E SS K C1 R1 C2 R2 e,
      prec_store_typing SS S ->
      prec_eval_typing Γ' S K (C1 # R1) (C2 # R2) ->
      prec_typing Γ S e (C1 # R1) ->
      env_well_typed S E Γ ->
      prec_state_typing ⟨ (e, E) | SS | K ⟩ (C2 # R2).

Hint Constructors prec_store_typing prec_eval_typing prec_state_typing : core.
Hint Resolve prec_typing_var prec_typing_app prec_typing_tapp prec_typing_box prec_typing_unbox : core.

Lemma prec_typing_implies_typing : forall Γ S e T,
  prec_typing Γ S e T ->
  typing Γ S e T.
Proof with eauto 3.
  intros * PTyp.
  dependent induction PTyp...
Qed.

Lemma prec_store_typing_implies_store_typing : forall SS S,
  prec_store_typing SS S ->
  store_typing SS S.
Proof with eauto using prec_typing_implies_typing.
  intros.
  dependent induction H...
Qed.

Lemma prec_eval_typing_implies_eval_typing : forall Γ S K T1 T2,
  prec_eval_typing Γ S K T1 T2 ->
  eval_typing Γ S K T1 T2.
Proof with eauto using prec_typing_implies_typing,
  prec_store_typing_implies_store_typing.
  intros * PTyp.
  dependent induction PTyp...
Qed.

Lemma prec_state_typing_implies_state_typing : forall s T,
  prec_state_typing s T ->
  state_typing s T.
Proof with eauto using prec_eval_typing_implies_eval_typing,
  prec_store_typing_implies_store_typing,
  prec_typing_implies_typing.
  intros * PTyp.
  dependent induction PTyp...
Qed.

Lemma prec_typing_regular : forall Γ S e T,
  prec_typing Γ S e T ->
  wf_store_ctx S /\ wf_ctx Γ S /\ expr e /\ wf_typ Γ S T.
Proof with eauto 3.
  intros * PTyp.
  apply prec_typing_implies_typing in PTyp.
  eapply typing_regular in PTyp...
Qed.

Lemma prec_typing_sub_typing : forall Γ S e T1 T2,
  prec_typing Γ S e T1 ->
  typing Γ S e T2 ->
  sub Γ S T1 T2.
Proof with eauto 5 using sub_reflexivity, binds_unique, subcapt_reflexivity, subst_ct_fresh.
  intros * PTyp Typ.
  generalize dependent T1.
  induction Typ; intros.
  - intros...
    inverts PTyp.
    epose proof (binds_unique _ _ _ _ H0 H5).
    inverts H1.
    apply sub_reflexivity...
    epose proof (wf_typ_from_binds_typ _ _ _ _ H2 H5).
    inverts H1.
    constructor...
  - intros...
    forwards (WfStore & WfCtx & _ & WfT): prec_typing_regular PTyp.
    inverts PTyp.
    inverts H8. inverts WfT.
    constructor...
    + pick fresh z and apply sub_arr...
    + pick fresh z and apply type_arr...
      specialize (H9 z ltac:(fsetdec)).
      specialize (H1 z ltac:(fsetdec) _ H9).
      destruct (sub_regular _ _ _ _ H1) as [_ [_ [_ ?]]].
      eapply type_from_wf_typ...
  - inverts PTyp.
    specialize (IHTyp1 _ H3).
    specialize (IHTyp2 _ H5).
    inverts IHTyp1. inverts H8...
    pick fresh z and specialize H17.
    pick fresh y.
    replace T with (subst_ct y (cse_fvar z) T) in H17.
    replace T0 with (subst_ct y (cse_fvar z) T0) in H17.
    rewrite subst_ct_open_ct_var in H17...
    rewrite subst_ct_open_ct_var in H17...
    rewrite_env (nil ++ [(z, bind_typ (D # Q))] ++ Γ) in H17.
    eapply sub_through_subst_ct with (C := exp_cv x) in H17.
    simpl_env in H17.
    rewrite <- subst_ct_fresh with (x := y) (c := cse_fvar z) in H17.
    rewrite <- subst_ct_fresh with (x := y) (c := cse_fvar z) in H17.
    rewrite <- subst_ct_intro in H17...
    rewrite <- subst_ct_intro in H17...
    + eapply notin_open_ct_rec_fv_ct...
    + eapply notin_open_ct_rec_fv_ct...
    + epose proof (typing_var_implies_binds_typ _ _ _ _ _ Typ2).
      destruct H as [D' [Q' [Binds [Subcapt [_ [Sub PureR2]]]]]]...
    + erewrite subst_ct_fresh...
    + erewrite subst_ct_fresh...
  - inverts PTyp.
    pick fresh x and specialize H9.
    specialize (H0 x ltac:(fsetdec) _ H9).
    rewrite_env (nil ++ [(x, bind_typ (C1 # R1))] ++ Γ) in H0.
    apply sub_through_subst_ct with (C := cse_bot) in H0.
    simpl_env in H0.
    rewrite <- subst_ct_fresh with (x := x) (c := cse_bot) in H0...
    rewrite <- subst_ct_fresh with (x := x) (c := cse_bot) in H0...
    constructor...
  - forwards (WfStore & WfCtx & _ & WfT): prec_typing_regular PTyp.
    inverts PTyp.
    inverts WfT.
    constructor; auto.
    + apply subcapt_reflexivity...
    + pick fresh x and apply sub_all...
    + pick fresh X and apply type_all...
      specialize (H10 X ltac:(fsetdec)).
      specialize (H2 X ltac:(fsetdec) _ H10).
      destruct (sub_regular _ _ _ _ H2) as [_ [_ [_ ?]]].
      eapply type_from_wf_typ...
  - inverts PTyp.
    specialize (IHTyp _ H4).
    inverts IHTyp. inverts H9.
    pick fresh X and specialize H15.
    rewrite_env (nil ++ [(X, bind_sub Q)] ++ Γ) in H15.
    epose proof (sub_through_subst_tt _ _ _ _ _ _ _ _ H15 H).
    simpl_env in H0.
    unfold open_tt in H0.
    erewrite <- subst_tt_intro_rec in H0...
    erewrite <- subst_tt_intro_rec in H0...
  - inverts PTyp.
    specialize (IHTyp _ H1).
    constructor...
  - inverts PTyp.
    specialize (IHTyp _ H4).
    inverts IHTyp. inverts H9...
  - eapply sub_transitivity with (Q := R)...
Qed.

Hint Extern 1 (wf_typ ?E ?S ?T) =>
  match goal with
  | H: prec_typing ?E ?S _ ?T |- _ => apply (proj2 (proj2 (proj2 (prec_typing_regular _ _ _ _ H))))
  end
: core.

Hint Extern 1 (wf_ctx ?E ?S) =>
  match goal with
  | H: prec_typing _ _ _ _ |- _ => apply (proj1 (proj2 (prec_typing_regular _ _ _ _ H)))
  end
: core.

Lemma prec_typing_weakening : forall Γ Θ Δ e T S,
  prec_typing (Δ ++ Γ) S e T ->
  wf_ctx (Δ ++ Θ ++ Γ) S ->
  prec_typing (Δ ++ Θ ++ Γ) S e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_ctx_typ,
                       sub_weakening,
                       subcapt_weakening.
  intros * PTyp. remember (Δ ++ Γ).
  generalize dependent Δ.
  induction PTyp; intros Δ EQ Ok; subst...
  - Case "typing_abs".
    pick fresh X and apply prec_typing_abs...
    lapply (H0 X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply H1...
  - Case "typing_let".
    pick fresh X and apply prec_typing_let...
    lapply (H X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply (H0 X)...
  - Case "typing_tabs".
    pick fresh X and apply prec_typing_tabs...
    lapply (H1 X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply H2...
  - Case "typing_box".
    apply prec_typing_box...
    simpl_env in H.
    assert (Δ ++ Γ = Δ ++ Γ) by reflexivity.
    specialize (IHPTyp Δ H0 Ok).
    inversion IHPTyp...
  - Case "typing_unbox".
    apply prec_typing_unbox...
    apply wf_cse_weakening...
Qed.

