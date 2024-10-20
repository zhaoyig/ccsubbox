(** Support here for Capture Sets, a.k.a a record
    of free and bound variables tracking which variables
    are captured by a particualar type. *)

Require Import Metatheory.
Require Import Tactics.

Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FSetFacts.
Require Import Atom.
Require Import Nat.
Require Export Bool.

Create HintDb csets.

(** ************************************************** *)
(** Definition of Capture Sets *)
(** ************************************************** *)

(** A captureset -- a triple of free variables,
    bound variables, and if we contain the special
    `universal` variable. *)
(* Inductive cap : Type :=
  | cset_set : atoms -> nats -> bool -> cap. *)

Inductive cse : Set :=
  | cse_top : cse
  | cse_bvar : nat -> cse
  | cse_fvar : atom -> cse
  | cse_join : cse -> cse -> cse
  | cse_bot : cse
.

(** ************************************************** *)
(** Constructors *)
(** ************************************************** *)

Declare Scope cse_shorthand.

Notation "{}" := (cse_bot) : cse_shorthand.
Notation "{*}" := (cse_top) : cse_shorthand.

(** ************************************************** *)
(** Selectors *)
(** ************************************************** *)

Fixpoint cse_fvars C :=
  match C with
  | cse_fvar a => AtomSet.F.singleton a
  | cse_join c1 c2 => AtomSet.F.union (cse_fvars c1) (cse_fvars c2)
  | _ => AtomSet.F.empty  
  end.          

Notation "`cse_fvars` C" := (cse_fvars C)
                                (at level 10, C at level 9) : cse_shorthand.

Fixpoint cse_bvars C :=
  match C with
  | cse_bvar k => NatSet.F.singleton k
  | cse_join c1 c2 => NatSet.F.union (cse_bvars c1) (cse_bvars c2)
  | _ => NatSet.F.empty  
  end.

Notation "`cse_bvars` C" := (cse_bvars C)
                                (at level 10, C at level 9) : cse_shorthand.

Fixpoint cse_uvar C :=
  match C with
  | cse_top => true
  | cse_join c1 c2 => orb (cse_uvar c1) (cse_uvar c2)
  | _ => false
  end.

Notation "`cse_uvar` C" := (cse_uvar C)
                                (at level 10, C at level 9) : cse_shorthand.


(** ************************************************** *)
(** Operations *)
(** ************************************************** *)

(* Definition cset_lvar (l : atom) :=
  (cset_set AtomSet.F.empty NatSet.F.empty (AtomSet.F.singleton l)). *)

(** Predicates for determining if a capture set explicity references
    a variable -- used for determining if a capture set is well formed.
    Don't use these predicates for determining if a capture set
    captures a variable, as one needs to also test cset_universal. *)

Open Scope cse_shorthand.

(** Capture set unions are what you'd expect. *)
Definition cse_union (c1 c2 : cse) : cse :=
  cse_join c1 c2.

(* Definition cse_subset_dec (C D : cse) := *)
(*   AtomSet.F.subset (`cse_fvars` C) (`cse_fvars` D) *)
(*     && NatSet.F.subset (`cse_bvars` C) (`cse_bvars` D) *)
(*     && (implb (`cse_uvar` C) (`cse_uvar` D)). *)

Notation "C `u` D" := (cse_union C D) (at level 69) : cse_shorthand.

Fixpoint remove_bvar (k : nat) (C : cse) :=
  match C with
  | cse_top => C
  | cse_fvar a => C
  | cse_join c1 c2 => cse_join (remove_bvar k c1) (remove_bvar k c2)
  | cse_bvar k' => if (k === k') then cse_bot else C
  | cse_bot => C
  end.

Fixpoint remove_all_bvars (C : cse) :=
  match C with
  | cse_top => C
  | cse_fvar a => C
  | cse_join c1 c2 => cse_join (remove_all_bvars c1) (remove_all_bvars c2)
  | cse_bvar _ => cse_bot
  | cse_bot => C
  end.

(* Notation "C A`\` x" := (remove_fvar x C) *)
(*                          (at level 69) : cset_shorthand. *)
Notation "x A`in` C" := (AtomSet.F.In x (`cse_fvars` C))
                          (at level 69) : cse_shorthand.
Notation "x A`mem` C" := (AtomSet.F.mem x (`cse_fvars` C)) (at level 69) : cse_shorthand.

Notation "C N`\` k" := (remove_bvar k C)
                         (at level 69) : cse_shorthand.
Notation "k N`in` C" := (NatSet.F.In k (`cse_bvars` C))
                          (at level 69) : cse_shorthand.
Notation "k N`mem` C" := (NatSet.F.mem k (`cse_bvars` C))
                           (at level 69) : cse_shorthand.

(* Notation "`* mem` C" := (`cse_uvar` C) *)
(*                            (at level 10, only parsing) : cse_shorthand. *)
(* Notation "`* in` C" := (`cse_uvar` C = true) *)
(*                            (at level 10) : cse_shorthand. *)


Notation "`cse_references_bvar` k c" :=
  (k N`in` c)
    (at level 10, k at level 9, c at level 9, only parsing) : cse_shorthand.
Notation "`cse_references_bvar_dec` k c" :=
  (k N`mem` c)
    (at level 10, k at level 9, c at level 9, only parsing) : cse_shorthand.
Notation "`cse_remove_bvar` k c" :=
  (c N`\` k)
    (at level 10, k at level 9, c at level 9, only parsing) : cse_shorthand.
Notation "`cse_remove_all_bvars` c" :=
  (remove_all_bvars c)
    (at level 10, c at level 9, only parsing) : cse_shorthand.

Notation "`cse_references_fvar` a c" :=
  (a A`in` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cse_shorthand.
Notation "`cse_references_fvar_dec` a c" :=
  (a A`mem` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cse_shorthand.

Inductive cse_all_not_top: cse -> Prop :=
  | cse_all_not_top_fvar: forall a,
      cse_all_not_top (cse_fvar a)
  | cse_all_not_top_bvar: forall n,
      cse_all_not_top (cse_bvar n)
  | cse_all_not_top_join: forall c1 c2,
      cse_all_not_top c1 ->
      cse_all_not_top c2 ->
      cse_all_not_top (cse_join c1 c2)
  | cse_all_not_top_bot:
    cse_all_not_top cse_bot.

Fixpoint open_cse (k : nat) (c : cse) (d : cse) : cse :=
  match d with
  | cse_top => cse_top
  | cse_bot => cse_bot
  | cse_bvar k' => if k === k' then c else d
  | cse_fvar _ => d
  | cse_join d1 d2 => cse_join (open_cse k c d1) (open_cse k c d2)
end.

Fixpoint subst_cse (a : atom) (c : cse) (d: cse) : cse :=
  match d with
  | cse_top => cse_top
  | cse_bot => cse_bot
  | cse_bvar _ => d
  | cse_fvar a' => if a == a' then c else d
  | cse_join d1 d2 => cse_join (subst_cse a c d1) (subst_cse a c d2)
end.



(* Check (fun x =>  fun N => x N`in` N). *)
(* Check (fun C D x => (cset_union D (cset_remove_fvar x C))). *)

Declare Scope experimental_set_scope.

Notation "{ x 'as' A}" := (cse_fvar x) : experimental_set_scope.
Notation "{ x 'as' N}" := (cse_bvar x) : experimental_set_scope.

Inductive cset : cse -> Prop :=
  | cset_top :
      cset cse_top
  | cset_fvar : forall (X : atom),
      cset (cse_fvar X)
  | cset_join : forall Q1 Q2,
      cset Q1 ->
      cset Q2 ->
      cset (cse_join Q1 Q2)
  | cset_bot :
      cset cse_bot
.

(* Definition capt (c : cse) : Prop := cset c. *)

(** ************************************************** *)
(** Properties *)
(** ************************************************** *)

(* Lemma cse_fvars_capt: forall (x: atom), *)
(*   capt (cse_fvar x). *)
(* Proof. intros. unfold capt. simpl. fnsetdec. Qed. *)

Lemma cse_fvars_join_union : forall (C1: cse) (C2: cse),
  `cse_fvars` (cse_join C1 C2) = AtomSet.F.union (`cse_fvars` C1) (`cse_fvars` C2).
Proof. auto. Qed.

Lemma subst_cse_fresh : forall x C1 C2,
  x `notin` (cse_fvars C1) ->
  C1 = subst_cse x C2 C1.
Proof with eauto.
  intros.
  symmetry.
  induction C1; simpl...
  (* C1 is an fvar *)
  - destruct (x == a).
    + rewrite e in H. simpl in H. fsetdec.
    + auto.
  (* C1 is a join *)
  - rewrite cse_fvars_join_union in H.
    notin_simpl.
    rewrite IHC1_1...
    rewrite IHC1_2...
Qed.

Lemma empty_union_empty : forall C1 C2,
  NatSet.F.Empty (C1 `u`N C2) ->
  NatSet.F.Empty C1 /\ NatSet.F.Empty C2.
Proof with eauto.
  intros.
  split; fnsetdec.
Qed.

Lemma open_cse_cset : forall i C c,
  cset C ->
  C = open_cse i c C.
Proof with eauto*.
  intros i C c H.
  induction H; simpl in *...
Qed.

Lemma subst_cc_intro_rec : forall x (C : cse) U k,
  x `notin` (`cse_fvars` C) ->
  open_cse k U C = subst_cse x U (open_cse k (cse_fvar x) C).
Proof with auto*.
  intros * NotIn.
  induction C; simpl...
  - destruct (k === n); simpl...
    + destruct (x == x); auto...
  - destruct (x == a); simpl...
    + rewrite e in NotIn. simpl in NotIn. fsetdec.
  - f_equal; rewrite cse_fvars_join_union in NotIn; notin_simpl.
    rewrite IHC1...
    rewrite IHC2...
Qed.

Lemma subst_cse_open_cset_rec : forall x k C1 C2 D,
  cset C1 ->
  subst_cse x C1 (open_cse k C2 D) = open_cse k (subst_cse x C1 C2) (subst_cse x C1 D).
Proof with eauto*.
  intros x k C1 C2 D Closed.
  induction D; auto; simpl.
  - destruct (k === n); simpl; reflexivity.
  - destruct (x == a); simpl; subst... apply open_cse_cset. apply Closed.
  - f_equal; auto. 
Qed.

(* Definition cse_subset_prop (c : cse) (d : cse) : Prop := *)
(*   AtomSet.F.Subset (`cse_fvars` c) (`cse_fvars` d) *)
(*     /\ NatSet.F.Subset (`cse_bvars` c) (`cse_bvars` d) *)
(*     /\  (leb (`cse_uvar` c) (`cse_uvar` d)). *)
(**)
(* Lemma subset_union : forall C1 C2 D1 D2, *)
(*   cse_subset_prop C1 D1 -> *)
(*   cse_subset_prop C2 D2 -> *)
(*   cse_subset_prop (cse_union C1 C2) (cse_union D1 D2). *)
(* Proof. *)
(*   intros. *)
(*   destruct C1. destruct C2; *)
(*   destruct H as [H1C1 [H2C1 H3C1]]; destruct H0 as [H1C2 [H2C2 H3C2]]; *)
(*   repeat split; try intuition. *)
(*   - repeat split; destruct H as [H1C1 [H2C1 H3C1]]; destruct H0 as [H1C2 [H2C2 H3C2]]; try intuition. *)
(*   simpl. destruct C2; simpl; simpl in *; auto. *)
(*     + intuition. *)
(*     + destruct (`cse_uvar` C2_1 || `cse_uvar` C2_2); simpl; auto. *)
(*       simpl in H3C2. intuition. *)
(*   - repeat split; destruct H as [H1C1 [H2C1 H3C1]]; destruct H0 as [H1C2 [H2C2 H3C2]]; try intuition. *)
(*     simpl. destruct (`cse_uvar` C2); auto. *)
(*     intuition. *)
(*   - repeat split; destruct H as [H1C1 [H2C1 H3C1]]; destruct H0 as [H1C2 [H2C2 H3C2]]; try intuition. *)
(*     simpl. simpl in *. destruct (`cse_uvar` C1_1 || `cse_uvar` C1_2); intuition. *)
(*     simpl. destruct (`cse_uvar` C2); auto. *)
(*     intuition. *)
(*   - repeat split; destruct H as [H1C1 [H2C1 H3C1]]; destruct H0 as [H1C2 [H2C2 H3C2]]; try intuition. *)
(*     simpl. destruct (`cse_uvar` C2); intuition. *)
(* Qed. *)

Lemma subst_cse_union : forall x D C1 C2,
  subst_cse x D (cse_union C1 C2) = (cse_union (subst_cse x D C1) (subst_cse x D C2)).
Proof with eauto.
  intros.
  induction C1; simpl...
Qed.

(** ************************************************** *)
(** Logical Predicates *)
(** ************************************************** *)

(* Definition cse_empty (c : cse) : Prop := *)
(*   AtomSet.F.Empty (`cse_fvars` c) /\ NatSet.F.Empty (`cse_bvars` c) /\ *)
(*     ((`cse_uvar` c) = false). *)

(* Definition cse_subset_prop (c : cse) (d : cse) : Prop := *)
(*   AtomSet.F.Subset (`cse_fvars` c) (`cse_fvars` d) *)
(*     /\ NatSet.F.Subset (`cse_bvars` c) (`cse_bvars` d) *)
(*     /\  (leb (`cse_uvar` c) (`cse_uvar` d)). *)

(** ************************************************** *)
(** Properties *)
(** ************************************************** *)

(* Section Props.
  Variable x y a f : atom.
  Variable l m R : bool.
  Variable A A1 A2 : atoms.
  Variable k n : nat.
  Variable N N1 N2 : nats.
  Variable C D C1 C2 C3 : cap.

  Lemma cset_bvar_mem_iff :
    `cset_references_bvar` k C <-> `cset_references_bvar_dec` k C = true.
  Proof.
    destruct C ;
      simpl in *; intuition.
  Qed.

  Lemma cset_fvar_mem_iff :
    `cset_references_fvar` a C <-> `cset_references_fvar_dec` a C = true.
  Proof.
    destruct C ;
      simpl in *; intuition.
  Qed.

  Lemma cset_univ_mem_iff :
    `cset_references_univ` C <-> `cset_references_univ_dec` C = true.
  Proof.
    destruct C;
    reflexivity.
  Qed.

  Lemma cset_bvar_not_mem_iff :
    ~ `cset_references_bvar` k C <-> `cset_references_bvar_dec` k C = false.
  Proof.
    destruct C ; rewrite <- NatSetFacts.not_mem_iff; fnsetdec.
  Qed.

  Lemma cset_fvar_not_mem_iff :
    ~ `cset_references_fvar` a C <-> `cset_references_fvar_dec` a C = false.
  Proof.
    destruct C ;
      split; intros; simpl in *; intuition.
      rewrite <- AtomSetFacts.not_mem_iff; fsetdec.
      rewrite <- AtomSetFacts.not_mem_iff in H; fsetdec.
  Qed.

  Lemma cset_univ_not_mem_iff :
    ~ `cset_references_univ` C <-> `cset_references_univ_dec` C = false.
  Proof.
    destruct C;
      split.
    intro; destruct b; auto*.
    intro; subst; auto.
  Qed.

  Lemma fvars_1 : `cset_fvars` (cset_set A N R) = A.
  Proof. trivial. Qed.

  Lemma bvars_1 : `cset_bvars` (cset_set A N R) = N.
  Proof. trivial. Qed.

  Lemma uvars_1 : `cset_uvar` (cset_set A N R) = R.
  Proof. trivial. Qed.

  Lemma fvars_union_1 : `cset_fvars` (cset_union C D) = AtomSet.F.union (`cset_fvars` C) (`cset_fvars` D).
  Proof. trivial. Qed.

  Lemma bvars_union_1 : `cset_bvars` (cset_union C D) = NatSet.F.union (`cset_bvars` C) (`cset_bvars` D).
  Proof. trivial. Qed.

  Lemma uvar_union_1 : `cset_uvar` (cset_union C D) = orb (`cset_uvar` C) (`cset_uvar` D).
  Proof. trivial. Qed.

  Lemma remove_fvar_1 : `cset_remove_fvar` x (cset_set A N R) = (cset_set (AtomSet.F.remove x A) N R).
  Proof. intros. simpl in *. trivial. Qed.

  Lemma remove_bvar_1 : `cset_remove_bvar` k (cset_set A N R) = (cset_set A (NatSet.F.remove k N) R).
  Proof. intros. simpl in *. trivial. Qed.

  Lemma mem_bvar_1 : `cset_references_bvar` k C -> `cset_references_bvar_dec` k C = true.
  Proof. rewrite cset_bvar_mem_iff; trivial. Qed.

  Lemma mem_bvar_2 : `cset_references_bvar_dec` k C = true -> `cset_references_bvar` k C.
  Proof. rewrite <- cset_bvar_mem_iff; trivial. Qed.

  Lemma mem_fvar_1 : `cset_references_fvar` a C -> `cset_references_fvar_dec` a C = true.
  Proof. rewrite cset_fvar_mem_iff; trivial. Qed.

  Lemma mem_fvar_2 : `cset_references_fvar_dec` a C = true -> `cset_references_fvar` a C.
  Proof. rewrite <- cset_fvar_mem_iff; trivial. Qed.

  Lemma mem_uvar_1 : `cset_references_univ` C -> `cset_references_univ_dec` C = true.
  Proof. trivial. Qed.

  Lemma mem_uvar_2 : `cset_references_univ_dec` C = true -> `cset_references_univ` C.
  Proof. trivial. Qed.

  Lemma In_bvar_1 : k = n -> `cset_references_bvar` k C -> `cset_references_bvar` n C.
  Proof. intros; subst; trivial. Qed.

  Lemma In_fvar_1 : a = f -> `cset_references_fvar` a C -> `cset_references_fvar` f C.
  Proof. intros; subst; trivial. Qed.

  Lemma Is_empty : cset_empty {}.
  Proof. repeat split. fsetdec. fnsetdec. Qed.

  Lemma union_fvar_1 : `cset_references_fvar` x (cset_union C D) -> `cset_references_fvar` x C \/ `cset_references_fvar` x D.
  Proof. intros. unfold cset_union in *; simpl in *. fsetdec. Qed.

  Lemma union_fvar_2 : `cset_references_fvar` x C -> `cset_references_fvar` x (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fsetdec. Qed.

  Lemma union_fvar_3 : `cset_references_fvar` x D -> `cset_references_fvar` x (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fsetdec. Qed.

  Lemma union_bvar_1 : `cset_references_bvar` k (cset_union C D) -> `cset_references_bvar` k C \/ `cset_references_bvar` k D.
  Proof. intros. unfold cset_union in *; simpl in *. fnsetdec. Qed.

  Lemma union_bvar_2 : `cset_references_bvar` k C -> `cset_references_bvar` k (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fnsetdec. Qed.

  Lemma union_bvar_3 : `cset_references_bvar` k D -> `cset_references_bvar` k (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fnsetdec. Qed.

  Lemma union_uvar_1 : `cset_references_univ` (cset_union C D) ->
    `cset_references_univ` C \/ `cset_references_univ` D.
  Proof. intros. unfold cset_union in *; simpl in *.
    rewrite orb_true_iff in H; auto*.
  Qed.

  Lemma union_uvar_2 : `cset_references_univ` C -> `cset_references_univ` (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. intro.
    rewrite orb_true_iff. auto. Qed.

  Lemma union_uvar_3 : `cset_references_univ` D -> `cset_references_univ` (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. intro.
    rewrite orb_true_iff. auto. Qed.
  
  Lemma union_sub_1 : cset_subset_prop C D -> cset_union D C = D.
  Proof.
    unfold cset_union, cset_subset_prop.
    intros. destruct C; destruct D; simpl; f_equal.
    fsetdec. fnsetdec.
      destruct b; destruct b0; auto*.
  Qed.

  Lemma union_sub_2 : cset_subset_prop C D -> D = cset_union D C.
  Proof.
    unfold cset_union, cset_subset_prop.
    intros. destruct C; destruct D; simpl; f_equal.
    fsetdec. fnsetdec.
      destruct b; destruct b0; auto*.
  Qed.

  Lemma union_subset_distribute_1 : cset_subset_prop C1 C2 -> cset_subset_prop (cset_union C1 D) (cset_union C2 D).
  Proof.
    intros. unfold cset_subset_prop in *; inversion H as [Sub_F [Sub_B Sub_A]];
    unfold cset_union in *; destruct C1; destruct C2.
    repeat split; try fsetdec; try fnsetdec.
      destruct b; destruct b0; unfold leb in *; simpl in *; destruct D; destruct b; auto*.
  Qed.

End Props. *)

(* TODO defined here to avoid all the implicit arguments *)
(* Lemma subset_univ_1 : forall R C,
  cset_subset_prop R C -> `cset_references_univ` R -> `cset_references_univ` C.
Proof. intros.
  destruct H as [_ [_ H]]. destruct R;
    destruct C; unfold leb in *; destruct b; destruct b0; auto*. Qed.

Hint Rewrite
  fvars_1 bvars_1
  fvars_union_1 bvars_union_1
  remove_fvar_1 remove_bvar_1
: csets.


Hint Resolve
  mem_bvar_1 mem_fvar_1 mem_uvar_1 Is_empty
  union_fvar_1 union_fvar_2 union_fvar_3
  union_bvar_1 union_bvar_2 union_bvar_3
  union_uvar_1 union_uvar_2 union_uvar_3
  union_sub_1 union_sub_2 union_subset_distribute_1
  subset_univ_1
: core.

Hint Immediate In_bvar_1 In_fvar_1 mem_bvar_2 mem_fvar_2 mem_uvar_2 : core.

(* Some subset properties *)
Lemma subset_refl : forall C,
  cset_subset_prop C C.
Proof.
  intros. unfold cset_subset_prop. repeat split. fsetdec. fnsetdec.
    unfold leb; destruct C; destruct b; auto*.
Qed.

Lemma subset_union_left : forall C1 C2,
  cset_subset_prop C1 (cset_union C1 C2).
Proof.
  intros. destruct C1. destruct C2. unfold cset_subset_prop, cset_union.
  repeat split. fsetdec. fnsetdec.
    destr_bool.
Qed.

Lemma subset_union_right : forall C1 C2,
  cset_subset_prop C2 (cset_union C1 C2).
Proof.
  intros. destruct C1. destruct C2. unfold cset_subset_prop, cset_union.
  repeat split. fsetdec. fnsetdec.
    destr_bool.
Qed.

Lemma subset_union : forall C1 C2 D1 D2,
  cset_subset_prop C1 D1 ->
  cset_subset_prop C2 D2 ->
  cset_subset_prop (cset_union C1 C2) (cset_union D1 D2).
Proof.
  intros.
  destruct C1. destruct C2.
  destruct H as [H1C1 [H2C1 H3C1]]. destruct H0 as [H1C2 [H2C2 H3C2]].
  repeat split.
  - apply AtomSetProperties.union_subset_3; fsetdec.
  - apply NatSetProperties.union_subset_3; fnsetdec.
  - unfold cset_union.
    destruct b, b0; simpl; intuition.
Qed.

Lemma subset_trans : forall A B C,
  cset_subset_prop A B -> cset_subset_prop B C -> cset_subset_prop A C.
Proof.
  intros * AB BC.
  inversion AB as [ABF [ABN ABU]]; subst; inversion BC as [BCF [BCN BCU]]; subst...
  repeat (econstructor; try fsetdec; try fnsetdec)...
  destruct A; destruct B; destruct C; destr_bool...
Qed.

Lemma subset_in : forall A B x,
  cset_subset_prop A B -> x A`in` A -> x A`in` B.
Proof.
  intros * AB xA.
  inversion AB as [ABF _]; subst...
  destruct A; destruct B; simpl.
  fsetdec.
Qed.

Hint Immediate subset_union_left subset_union_right  subset_refl: core.


(***********)
(* Tactics *)
(***********)

Ltac rewrite_set_facts_in H :=
  match type of H with
  | true = _ => symmetry in H
  | false = _ => symmetry in H
  | _ => idtac
  end;
  match type of H with
  | NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff in H
  | NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff in H
  | AtomSet.F.mem _ _ = true => rewrite <- AtomSetFacts.mem_iff in H
  | AtomSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff in H
  | `cset_references_bvar_dec` _ _ = true => rewrite <- cset_bvar_mem_iff in H
  | `cset_references_fvar_dec` _ _ = true => rewrite <- cset_fvar_mem_iff in H
  | `cset_references_univ_dec` _ _ = true => rewrite <- cset_univ_mem_iff in H
  | `cset_references_bvar_dec` _ _ = false => rewrite <- cset_bvar_not_mem_iff in H
  | `cset_references_fvar_dec` _ _ = false => rewrite <- cset_fvar_not_mem_iff in H
  | `cset_references_univ_dec` _ _ = false => rewrite <- cset_univ_not_mem_iff in H
  end;
  (** argh, unused arguments need to be discharged *)
  try apply NatSet.F.empty; try apply AtomSet.F.empty; try apply {}.

Ltac rewrite_set_facts_back_in H :=
  match type of H with
  | true = _ => symmetry in H
  | false = _ => symmetry in H
  | _ => idtac
  end;
  match type of H with
  | NatSet.F.In _ _          => rewrite -> NatSetFacts.mem_iff in H
  | (~ NatSet.F.In _ _)      => rewrite -> NatSetFacts.not_mem_iff in H
  | AtomSet.F.In _ _         => rewrite -> AtomSetFacts.mem_iff in H
  | (~ AtomSet.F.In _ _)     => rewrite -> AtomSetFacts.not_mem_iff in H
  | `cset_references_bvar` _ _ => rewrite -> cset_bvar_mem_iff in H
  | `cset_references_fvar` _ _ => rewrite -> cset_fvar_mem_iff in H
  | `cset_references_univ` _ _ => rewrite -> cset_univ_mem_iff in H
  | (~ `cset_references_bvar` _ _) => rewrite -> cset_bvar_not_mem_iff in H
  | (~ `cset_references_fvar` _ _) => rewrite -> cset_fvar_not_mem_iff in H
  | (~ `cset_references_univ` _ _) => rewrite -> cset_univ_not_mem_iff in H
  end;
  (** argh, unused arguments need to be discharged *)
  try apply NatSet.F.empty; try apply AtomSet.F.empty; try apply {}.

Ltac simpl_in_cset :=
  let go H := rewrite_set_facts_back_in H; try rewrite H in *; rewrite_set_facts_in H in
  match goal with
  | H: `cset_references_bvar_dec` ?I ?C = ?B |- _ => try rewrite H in *
  | H: ~ (`cset_references_bvar` _ _) |- _ => go H
  | H: (`cset_references_bvar` _ _)   |- _ => go H
  | H: ~ (`cset_references_fvar` _ _) |- _ => go H
  | H: (`cset_references_fvar` _ _)   |- _ => go H
  | H: ~ (`cset_references_univ` _ _) |- _ => go H
  | H: (`cset_references_univ` _ _)   |- _ => go H
  end.

Ltac destruct_set_mem_univ bs :=
  destruct (`cset_references_univ_dec` bs) eqn:H; rewrite_set_facts_in H; trivial.

Ltac destruct_set_mem a bs :=
  match type of bs with
  | AtomSet.F.t =>
    let H := fresh a "In" in
    destruct (AtomSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | NatSet.F.t =>
    let H := fresh a "In" in
    destruct (NatSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | cse =>
    match type of a with
    | atom =>
      let H := fresh a "In" in
      destruct (`cset_references_fvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    (** why argh *)
    | AtomSet.F.elt =>
      let H := fresh a "In" in
      destruct (`cset_references_fvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    | nat =>
      let H := fresh a "In" in
      destruct (`cset_references_bvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    | NatSet.F.elt =>
      let H := fresh a "In" in
      destruct (`cset_references_bvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    end
  end.

Ltac find_and_destroy_set_mem :=
  try match goal with
  | H : _ |- context G [`cset_references_fvar_dec` ?X ?S] => destruct_set_mem X S
  | H : _ |- context G [`cset_references_bvar_dec` ?B ?S] => destruct_set_mem B S
  | H : _ |- context G [`cset_references_univ_dec` ?S] => destruct_set_mem_univ S
  | H : _ |- context G [AtomSet.F.mem ?X ?S] => destruct_set_mem X S
  | H : _ |- context G [NatSet.F.mem ?N ?S] => destruct_set_mem N S
  | H : context G [`cset_references_fvar_dec` ?X ?S] |- _ => destruct_set_mem X S
  | H : context G [`cset_references_bvar_dec` ?B ?S] |- _ => destruct_set_mem B S
  | H : context G [`cset_references_univ_dec` ?S] |- _ => destruct_set_mem_univ S
  | H : context G [AtomSet.F.mem ?X ?S] |- _ => destruct_set_mem X S
  | H : context G [NatSet.F.mem ?N ?S] |- _ => destruct_set_mem N S
  end.

Lemma funion_empty_idempotent : forall xs, xs `u`N {}N = xs.
Proof. intros. fnsetdec. Qed.

Lemma empty_funion_idempotent : forall xs, {}N `u`N xs = xs.
Proof. intros. fnsetdec. Qed.

Lemma union_empty_idempotent : forall xs, xs `u`A {}A = xs.
Proof. intros. fsetdec. Qed.

Lemma empty_union_idempotent : forall xs, {}A `u`A xs = xs.
Proof. intros. fsetdec. Qed.

Lemma false_or_idempotent : forall xs, false || xs = xs.
Proof. destr_bool. Qed.

Lemma or_false_idempotent : forall xs, xs || false = xs.
Proof. destr_bool. Qed.

Lemma true_or_true : forall xs, true || xs = true.
Proof. destr_bool. Qed.

Lemma or_true_true : forall xs, xs || true = true.
Proof. destr_bool. Qed.

Hint Rewrite
  funion_empty_idempotent empty_funion_idempotent
  union_empty_idempotent empty_union_idempotent
  or_false_idempotent false_or_idempotent
  true_or_true or_true_true
: csets.

Lemma cunion_empty_idempotent : forall xs, xs `u` {} = xs.
Proof. intros. destruct xs. unfold cset_union. autorewrite with csets; trivial. Qed.

Lemma empty_cunion_idempotent : forall xs, {} `u` xs = xs.
Proof. intros. destruct xs. unfold cset_union. autorewrite with csets; trivial. Qed.

Hint Rewrite cunion_empty_idempotent empty_cunion_idempotent : csets.

(* Lemma cset_concrete_union : forall xs ns us xs' ns' us',
  (cset_set xs ns us) `u` (cset_set xs' ns' us') =
  (cset_set (xs `u`A xs') (ns `u`N ns') (us || us')).
   Proof. intros. cbv [cset_union]. reflexivity. Qed. *)

Hint Rewrite cset_concrete_union : csets.

(* To be redefined later. *)
Ltac _csetsimpl_hook := idtac.

Ltac csetsimpl :=
  repeat (_csetsimpl_hook; subst; simpl; autorewrite with csets in * ).

Ltac csetsimplIn H :=
  repeat (subst; simpl in H; autorewrite with csets in H).

Tactic Notation "csetsimpl" "in" hyp(H) := csetsimplIn H.

Ltac find_and_destroy_cse :=
  try match goal with
    | C : cse |- _ => destruct C
  end.

Ltac discharge_empty :=
  try match goal with
    | H : AtomSet.F.Empty ?S |- _ =>
      assert (S = {}A) by fsetdec; subst; clear H; subst
    | H : NatSet.F.Empty ?S |- _ =>
      assert (S = {}N) by fnsetdec; subst; clear H; subst
  end.

Ltac csetdec :=
  try (progress (csetsimpl;
                 (** destroy set membership, if any *)
                 repeat find_and_destroy_set_mem;
                 repeat find_and_destroy_cse;
                 repeat discharge_empty;
                 (* unfold, if necessary *)
                 cbv [cset_union cset_subset_prop] in *;
                 (* split, if necessary *)
                 try f_equal;
                 try notin_solve; try fsetdec; try solve [exfalso; notin_solve];
                 try nnotin_solve; try fnsetdec; try solve [exfalso; nnotin_solve];
                 try solve [destr_bool]
                 );
       intuition (csetdec)).

(** Some more facts about Bool *)
Lemma leb_reflexive : forall xs,
  leb xs xs.
Proof. destr_bool. Qed.

Lemma leb_true : forall xs,
  leb xs true.
Proof. destr_bool. Qed.

Lemma false_leb : forall xs,
  leb false xs.
Proof. destr_bool. Qed.

Lemma andb_false_false : forall xs,
  andb xs false = false.
Proof. destr_bool. Qed.

Lemma false_andb_false : forall xs,
  andb false xs = false.
Proof. destr_bool. Qed.

Hint Resolve leb_reflexive leb_true false_leb andb_false_false false_andb_false : core. *)

(** ************************************************** *)
(** Locally Namelesss *)
(** ************************************************** *)


(* Lemma singleton_closed : forall f,
  capt (`cset_fvar` f).
Proof.
  unfold capt; fnsetdec.
Qed.

Lemma capt_empty_bvar : forall A N R,
  capt (cset_set A N R) ->
  N = {}N.
Proof.
  intros. unfold capt in *. fnsetdec.
Qed.

Lemma capt_concrete_cset : forall xs b,
  capt (cset_set xs {}N b).
Proof.
  intros. unfold capt. fnsetdec.
Qed.

Hint Unfold capt : core.
Hint Resolve capt_empty_bvar capt_concrete_cset : core. *)

(* Lemma subst_over_subset : forall C1 C2 D x,
  cset_subset_prop C1 C2 ->
  cset_subset_prop (subst_cset x D C1) (subst_cset x D C2).
Proof.
  intros.
  unfold cset_subset_prop in *.
  destruct H as [HF [HB HU]].
  cbv [subst_cset].
  csetdec...
Qed.

Lemma subst_subset_intro : forall C1 C2 x,
  (* C1 is closed *)
  capt C1 ->
  cset_subset_prop (`cset_fvar` x) C2 ->
  cset_subset_prop C1 (subst_cset x C1 C2).
Proof.
  intros.
  cbv [subst_cset].
  unfold capt in H.
  csetdec.
Qed.

Lemma subst_cset_union : forall x D C1 C2,
  subst_cset x D (cset_union C1 C2) = (cset_union (subst_cset x D C1) (subst_cset x D C2)).
Proof with eauto.
  intros.
  cbv [subst_cset].
  csetdec...
Qed.

Lemma subst_cset_singleton : forall x C,
  subst_cset x C (`cset_fvar` x) = C.
Proof.
  intros; cbv [subst_cset].
  csetdec.
Qed.

Lemma subst_cset_fresh : forall x C1 C2,
  x `notin` (`cset_fvars` C1) ->
  C1 = subst_cset x C2 C1.
Proof with eauto.
  intros.
  cbv [subst_cset].
  csetdec.
Qed.

Lemma singleton_univ :
  `cset_references_univ` {*}.
Proof with eauto.
  trivial.
Qed.

Lemma subst_cset_fresh_id : forall x X C,
  x <> X ->
  (subst_cset X C (`cset_fvar` x)) = (`cset_fvar` x).
Proof.
  intros.
  cbv [subst_cset].
  csetdec.
Qed.

Lemma subst_cset_union_id : forall x y D C1,
  x <> y ->
  subst_cset x D (cset_union C1 (`cset_fvar` y)) = (cset_union (subst_cset x D C1) (`cset_fvar` y)).
Proof with eauto.
  intros.
  rewrite <- (subst_cset_fresh_id y x D) at 2...
  apply subst_cset_union.
Qed.

Lemma subst_cset_univ : forall x C R,
  `cset_references_univ` R ->
  `cset_references_univ` (subst_cset x C R).
Proof with eauto.
  intros. cbv [subst_cset]. csetdec.
Qed.

Lemma open_cset_capt : forall i C c,
  capt C ->
  C = open_cset i c C.
Proof with eauto*.
  intros i C c H.
  unfold open_cset in *.
  unfold capt in H.
  csetdec.
Qed.

Lemma subst_cc_intro_rec : forall X (C : cap) U k,
  X `notin` (`cset_fvars` C) ->
  open_cset k U C = subst_cset X U (open_cset k (`cset_fvar` X) C).
Proof with auto*.
  intros * NotIn.
  cbv [open_cset subst_cset].
  csetdec.
Qed.

Lemma subst_cset_capt : forall Z C1 C,
  capt C1 ->
  capt C ->
  capt (subst_cset Z C1 C).
Proof.
  intros.
  cbv [subst_cset capt] in *.
  csetdec...
Qed.

Hint Resolve singleton_closed open_cset_capt subst_cset_capt : core.
Hint Rewrite subst_cset_singleton subst_cset_union : csets.

(** Automation *)
(* Lemma cset_eq_injectivity : forall a1 a2 n1 n2,
    a1 = a2 ->
    n1 = n2 ->
    cset_set a1 n1 = cset_set a2 n2.
Proof.
  intros. congruence.
   Qed. *)

Ltac fnset_mem_dec :=
  match goal with
  | |- true = _ => symmetry
  | |- false = _ => symmetry
  | |- _ => idtac
  end;
  match goal with
  | |- NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff; fnsetdec
  | |- NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff; fnsetdec
  end.

Ltac fset_mem_dec :=
  match goal with
  | |- true = _ => symmetry
  | |- false = _ => symmetry
  | |- _ => idtac
  end;
  match goal with
  | |- AtomSet.F.mem _ _ = true => rewrite <- AtomSetFacts.mem_iff; fsetdec
  | |- AtomSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff; fsetdec
  end.

Ltac cset_eq_dec :=
  apply cset_eq_injectivity; [try fsetdec | try fnsetdec].

Ltac destruct_if :=
  match goal with
  | |- context[if ?t then _ else _] =>
    destruct t eqn:?
  end.

Ltac destruct_if_in_as t id :=
  match type of t with
  | context[if ?t then _ else _] =>
    destruct t eqn:id
  end.

Tactic Notation "destruct_if" :=
  destruct_if.

Tactic Notation "destruct_if" "in" constr(t) "as" simple_intropattern(id) :=
  destruct_if_in_as t id.

Tactic Notation "destruct_if" "in" constr(t) :=
  destruct_if in t as ?.

Ltac destruct_match :=
  match goal with
  | |- context[match ?t with _ => _ end] =>
    destruct t eqn:?
  end.


(* ********************************************************************** *)
(** * #<a name="csetprops"></a># Properties of capture sets *)


Lemma open_cset_rec_capt_aux : forall c j V i U,
  i <> j ->
  capt V ->
  (andb (`cset_uvar` V) (`cset_uvar` U)) = false ->
  AtomSet.F.Empty (AtomSet.F.inter (`cset_fvars` V) (`cset_fvars` U)) ->
  open_cset j V c = open_cset i U (open_cset j V c) ->
  c = open_cset i U c.
Proof with eauto.
  intros * Hfresh Hempty HdisjointUniv HdisjointV Eq.
  unfold capt, open_cset, cset_union in *.
  csetdec; inversion Eq; autorewrite with csets...
  * assert (t `subset` t3). {
      intros e Het.
      assert (e `in` (t `union` t1 `union` t3)) by fsetdec.
      assert (AtomSet.F.Empty (AtomSet.F.inter t1 t)). {
        rewrite H. fsetdec.
      }
      assert (e `notin` t1) by fsetdec.
      rewrite <- H1 in H0. fsetdec.
    }
    fsetdec.
  * assert (NatSet.F.In i (NatSet.F.remove j t4)) by fnsetdec.
    assert (~ NatSet.F.In i (NatSet.F.remove i (NatSet.F.remove j t4))) by fnsetdec.
    assert (NatSet.F.In i t0). {
      destruct_set_mem i t0...
      assert (~ NatSet.F.In i (t0 `u`N (t4 `\`N j) `\`N i)) by
         fnsetdec.
      rewrite <- H2 in H5. fnsetdec.
    }
    assert (NatSet.F.Subset t0 t4). {
      intros e Het6.
      destruct (e === i); subst...
      assert (NatSet.F.In e (NatSet.F.union t0 (NatSet.F.remove i (NatSet.F.remove j t4)))). fnsetdec.
      rewrite <- H2 in H6...
      assert (e <> j) by fnsetdec.
      fnsetdec.
    }
    fnsetdec.
Qed.

Lemma subst_cset_open_cset_rec : forall x k C1 C2 D,
  capt C1 ->
  subst_cset x C1 (open_cset k C2 D) = open_cset k (subst_cset x C1 C2) (subst_cset x C1 D).
Proof with eauto*.
  intros x k C1 C2 D Closed.
  cbv [capt subst_cset open_cset] in *.
  csetdec.
Qed.

Lemma subst_cset_useless_repetition : forall x C1 C2 D,
  x `notin` `cset_fvars` C2 ->
  subst_cset x C1 (subst_cset x C2 D) = (subst_cset x C2 D).
Proof.
  intros.
  symmetry.
  eapply subst_cset_fresh with (C1 := subst_cset x C2 D)...
  cbv [subst_cset].
  csetdec...
Qed.


Lemma atoms_empty_union : forall xs ys,
  xs `u`A ys = {}A -> xs = {}A /\ ys = {}A.
Proof with eauto.
  intros.
  assert (AtomSet.F.Empty (xs `u`A ys)).
    rewrite H. fsetdec.
  split; fsetdec.
Qed.
Lemma atoms_empty_union_left : forall xs ys,
  xs `u`A ys = {}A -> xs = {}A.
Proof with eauto.
  intros. apply atoms_empty_union in H as [? ?]...
Qed.
Lemma atoms_empty_union_right : forall xs ys,
  xs `u`A ys = {}A -> ys = {}A.
Proof with eauto.
  intros. apply atoms_empty_union in H as [? ?]...
Qed.

Lemma nats_empty_union : forall xs ys,
  xs `u`N ys = {}N -> xs = {}N /\ ys = {}N.
Proof with eauto.
  intros.
  assert (NatSet.F.Empty (xs `u`N ys)).
    rewrite H. fnsetdec.
  split; fnsetdec.
Qed.
Lemma nats_empty_union_left : forall xs ys,
  xs `u`N ys = {}N -> xs = {}N.
Proof with eauto.
  intros. apply nats_empty_union in H as [? ?]...
Qed.
Lemma nats_empty_union_right : forall xs ys,
  xs `u`N ys = {}N -> ys = {}N.
Proof with eauto.
  intros. apply nats_empty_union in H as [? ?]...
Qed.

Lemma univ_empty_union : forall b b',
  b || b' = false -> b = false /\ b' = false.
Proof with eauto.
  intros.
  destr_bool...
Qed.
Lemma univ_empty_union_left : forall b b',
  b || b' = false -> b = false.
Proof with eauto.
  intros. apply univ_empty_union in H as [? ?]...
Qed.
Lemma univ_empty_union_right : forall b b',
  b || b' = false -> b' = false.
Proof with eauto.
  intros. apply univ_empty_union in H as [? ?]...
Qed.

Hint Resolve atoms_empty_union_left atoms_empty_union_right
              nats_empty_union_left nats_empty_union_right
              univ_empty_union_left univ_empty_union_right
  : core.

Lemma empty_cset_union : forall C1 C2,
  cset_union C1 C2 = {} ->
  C1 = {} /\ C2 = {}.
Proof with eauto.
  intros.
  destruct C1; destruct C2; simpl in H; try discriminate.
  inversion H; split; f_equal; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4...
Qed.

Lemma cset_subst_self : forall C x,
  subst_cset x C (`cset_fvar` x) = C.
Proof.
  intros.
  unfold subst_cset.
  csetdec.
Qed.

Lemma not_in_fv_cset_iff : forall x C,
  x A`mem` C = false -> x `notin` (`cset_fvars` C).
Proof.
  intros.
  csetdec.
Qed.

Lemma empty_over_union : forall N1 N2,
  {}N = NatSet.F.union N1 N2 ->
  {}N = N1 /\ {}N = N2.
Proof.
  intros.
  assert (NatSet.F.Empty (NatSet.F.union N1 N2)) by (rewrite <- H; fnsetdec).
  split; fnsetdec.
Qed.

Lemma cset_references_fvar_over_union : forall C1 C2 x,
  x A`in` (cset_union C1 C2) ->
  x A`in` C1 \/ x A`in` C2.
Proof with eauto*.
  intros * H.
  destruct (cset_union C1 C2) eqn:Hunion...
  unfold cset_union in *.
  destruct C1 eqn:HC1; destruct C2 eqn:HC2; subst...
  inversion Hunion...
  assert (x `in` (t1 `union` t3)) by (rewrite H1; eauto* )...
  apply AtomSetFacts.union_iff in H0; inversion H0; subst...
Qed.

Lemma subst_cset_distributive_across_union : forall z C D1 D2,
  subst_cset z C (cset_union D1 D2) =
  cset_union (subst_cset z C D1) (subst_cset z C D2).
Proof with eauto.
  intros.
  destruct D1; destruct D2.
  unfold cset_union, subst_cset.
  csetdec.
Qed.

Lemma notin_cset_fvars_distributive_over_cset_union : forall x C D,
  x `notin` `cset_fvars` (cset_union C D) ->
  x `notin` `cset_fvars` C /\
  x `notin` `cset_fvars` D.
Proof.
  intros.
  destruct C eqn:EQ__C;
    destruct D eqn:EQ__D;
    unfold cset_union in *; split.
  all : (easy || fsetdec).
Qed. *)
