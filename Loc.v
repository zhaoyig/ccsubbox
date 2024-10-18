(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

Require Import List.
Require Import Max.
Require Import OrderedType.
Require Import OrderedTypeEx.
Open Scope nat_scope.

Require Import FiniteSets.
Require Import FSetDecide.
Require Import FSetNotin.
Require Import ListFacts.


(* ********************************************************************** *)
(** * Definition *)

(** Locs are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on locs is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of locs.  The [Export LocImpl] line below allows
    us to refer to the type [loc] and its properties without having
    to qualify everything with "[LocImpl.]". *)

Module Type LOC.

  Parameter loc : Set.

  Parameter loc_fresh_for_list :
    forall (xs : list loc), {x : loc | ~ List.In x xs}.

  Declare Module Loc_as_OT : UsualOrderedType with Definition t := loc.

  Parameter eq_loc_dec : forall x y : loc, {x = y} + {x <> y}.

End LOC.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module LocImpl : LOC.

  (* begin hide *)

  Definition loc := nat.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y; auto with arith.
      simpl. induction z. intuition. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
      subst. auto with arith.
      auto using max_lt_r.
  Qed.

  Lemma loc_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). intuition. trivial.
  Qed.

  Module Loc_as_OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts Loc_as_OT.

  Definition eq_loc_dec : forall x y : loc, {x = y} + {x <> y} :=
    Facts.eq_dec.

  (* end hide *)

End LocImpl.

Export LocImpl.


(* ********************************************************************** *)
(** * Finite sets of locs *)


(* ********************************************************************** *)
(** ** Definitions *)

Module LocSet : FiniteSets.S with Module E := Loc_as_OT :=
  FiniteSets.Make Loc_as_OT.

(** The type [locs] is the type of finite sets of [loc]s. *)

Notation locs := LocSet.F.t.

(** Basic operations on finite sets of locs are available, in the
    remainder of this file, without qualification.  We use [Import]
    instead of [Export] in order to avoid unnecessary namespace
    pollution. *)

Import LocSet.F.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of locs. *)

Module LocSetDecide := FSetDecide.Decide LocSet.F.
Module LocSetNotin  := FSetNotin.Notin   LocSet.F.
Module LocSetFacts  := FSetFacts.Facts   LocSet.F.
Module LocSetProperties := FSetProperties.Properties LocSet.F.

(* *********************************************************************** *)
(** ** Tactics for working with finite sets of locs *)

(** The tactic [fsetdec] is a general purpose decision procedure
    for solving facts about finite sets of locs. *)

Ltac flsetdec := try apply LocSet.eq_if_Equal; LocSetDecide.fsetdec.

(** The tactic [notin_simpl] simplifies all hypotheses of the form [(~
    In x F)], where [F] is constructed from the empty set, singleton
    sets, and unions. *)

Ltac lnotin_simpl := LocSetNotin.notin_simpl_hyps.

(** The tactic [notin_solve], solves goals of the form [(~ In x F)],
    where [F] is constructed from the empty set, singleton sets, and
    unions.  The goal must be provable from hypothesis of the form
    simplified by [notin_simpl]. *)

Ltac lnotin_solve := LocSetNotin.notin_solve.


(* *********************************************************************** *)
(** ** Lemmas for working with finite sets of locs *)

(** We make some lemmas about finite sets of locs available without
    qualification by using abbreviations. *)

Notation eq_if_Equal        := LocSet.eq_if_Equal.
Notation lnotin_empty        := LocSetNotin.notin_empty.
Notation lnotin_singleton    := LocSetNotin.notin_singleton.
Notation lnotin_singleton_rw := LocSetNotin.notin_singleton_rw.
Notation lnotin_union        := LocSetNotin.notin_union.


(* ********************************************************************** *)
(** * Additional properties *)

(** One can generate an loc fresh for a given finite set of locs. *)

Lemma loc_fresh_for_set : forall L : locs, { x : loc | ~ In x L }.
Proof.
  intros L. destruct (loc_fresh_for_list (elements L)) as [a H].
  exists a. intros J. contradiction H.
  rewrite <- InA_iff_In. auto using elements_1.
Qed.


Lemma locset_subset_union : forall A1 A2 B1 B2,
  LocSet.F.Subset A1 A2 ->
  LocSet.F.Subset B1 B2 ->
  LocSet.F.Subset (LocSet.F.union A1 B1) (LocSet.F.union A2 B2).
Proof.
  intros.
  flsetdec.
Qed.

Lemma locset_union_right : forall A B C,
  LocSet.F.Subset A B ->
  LocSet.F.Subset (LocSet.F.union A C) (LocSet.F.union B C).
Proof.
  intros.
  flsetdec.
Qed.

Lemma singleton_set_eq : forall (x y : loc),
  singleton x = singleton y <-> x = y.
Proof.
  split; intros.
  * assert (LocSet.F.In y (singleton x)).
    { rewrite H. flsetdec. }
    flsetdec.
  * flsetdec.
Qed.
