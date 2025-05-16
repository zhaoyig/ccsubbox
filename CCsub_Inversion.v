Require Import Coq.Program.Equality.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.

(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall Γ S1 e1 T S,
  typing Γ S (λ (S1) e1) T ->
  forall U1 U2 C, sub Γ S T (C # (∀ (U1) U2)) ->
     sub Γ S U1 S1
  /\ exists S2, exists L, forall x, x ∉ L ->
    typing ([(x, bind_typ S1)] ++ Γ) S (open_ve e1 x (cse_fvar x)) (open_ct S2 (cse_fvar x)) /\
    wf_typ ([(x, bind_typ S1)] ++ Γ) S (open_ct U2 (cse_fvar x)) /\
    sub ([(x, bind_typ U1)] ++ Γ) S (open_ct S2 (cse_fvar x)) (open_ct U2 (cse_fvar x)).
Proof with auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_abs".
    inversion Sub; subst.
    inversion select (sub _ _ _ _); subst.
    split...
    exists T1.
    exists (L `u`A L0).
    intros y ?.
    rename select (forall x : atom, x ∉ L0 -> _) into Sub'.
    specialize (Sub' y ltac:(fsetdec)).
    repeat split...
    rewrite_nil_concat.
    eapply wf_typ_ignores_typ_bindings.
    applys sub_regular Sub'.
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall Γ S1 e1 T S,
  typing Γ S (Λ [S1] e1) T ->
  forall U1 U2 C, sub Γ S T (C # (∀ [U1] U2)) ->
     sub Γ S U1 S1
  /\ exists S2, exists L, forall X, X ∉ L ->
    typing ([(X, bind_sub U1)] ++ Γ) S (open_te e1 X) (open_tt S2 X) /\
    sub ([(X, bind_sub U1)] ++ Γ) S (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_tabs".
    inversion Sub; subst.
    inversion select (sub _ _ _ _); subst.
    split...
    exists T1.
    exists (L `union` L0).
    intros Y ?.
    repeat split...
    rewrite_nil_concat.
    eapply typing_narrowing with (Q := S1)...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

Lemma typing_inv_let : forall Γ e k T1 T2 S,
  typing Γ S (let= e : T1 in k) T2 ->
  exists C R,
    typing Γ S e (C # R)
    /\ exists L, forall x, x ∉ L ->
      typing ([(x, bind_typ (C # R))] ++ Γ) S (open_ve k x (cse_fvar x)) T2.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
  destruct (IHTyp e k T1 ltac:(reflexivity)) as [C [R0 [eTyp [L kTyp]]]].
  exists C, R0.
  split...
  exists (L `u`A dom Γ).
  intros y NotIn.
  specialize (kTyp y ltac:(clear - NotIn; fsetdec)).
  apply typing_sub with (R := R)...
  rewrite_env (∅ ++ [(y, bind_typ (C # R0))] ++ Γ).
  apply sub_weakening...
Qed.

Lemma typing_inv_app : forall Γ S (f x : atom) T,
  typing Γ S (f @ x) T ->
  exists C D Q U, typing Γ S f (C # (∀ (D # Q) U))
               /\ typing Γ S x (D # Q)
               /\ sub Γ S (open_ct U (cse_fvar x)) T.
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
    destruct (IHTyp f x ltac:(reflexivity) WfStore WfCtx WfR) as [C [D [Q [U [fTyp [xTyp Sub']]]]]].
    repeat eexists...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_tapp : forall Γ S (x : atom) V T,
  typing Γ S (x @ [V]) T ->
  exists C R U, typing Γ S x (C # (∀ [R] U))
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
    destruct (IHTyp x V eq_refl) as [C [R' [U [fTyp [lTyp Sub]]]]].
    exists C, R', U.
    repeat split...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_box : forall Γ S x T,
  typing Γ S (box x) T ->
  exists C R, typing Γ S x (C # R)
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
      apply wf_cse_free_vars_bound with (X := x) in H...
      destruct H as [T Binds].
      apply binds_In with (a := bind_typ T)...
    + apply sub_reflexivity...
  - Case "typing_sub".
    rename select (sub Γ S R T) into Sub.
    assert (WfR : wf_typ Γ S R) by applys sub_regular Sub.
    destruct (IHTyp x eq_refl WfStore WfCtx WfR) as [C [R' [lTyp [xSubΓ CRsubS]]]].
    exists C, R'.
    repeat split...
    apply sub_transitivity with (Q := R)...
Qed.

Lemma typing_inv_unbox : forall Γ S C x T,
  typing Γ S (exp_unbox C x) T ->
  exists R, typing Γ S x ({} # (□ (C # R)))
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
