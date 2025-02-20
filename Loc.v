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

(* ********************************************************************** *)
(** ** #<a name="pick_fresh"></a># Picking a fresh location *)

(** We define three tactics which, when combined, provide a simple
    mechanism for picking a fresh atom.  We demonstrate their use
    below with an example, the [example_pick_fresh] tactic.

   [(gather_atoms_with F)] returns the union of [(F x)], where [x]
   ranges over all objects in the context such that [(F x)] is
   well typed.  The return type of [F] should be [atoms].  The
   complexity of this tactic is due to the fact that there is no
   support in [Ltac] for folding a function over the context. *)

Ltac gather_locs_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | empty => gather FH
      | context [FH] => fail 1
      | _ => gather (union FH V)
      end
    | _ => V
    end in
  let L := gather empty in eval simpl in L.

(** [(beautify_fset V)] takes a set [V] built as a union of finite
    sets and returns the same set with empty sets removed and union
    operations associated to the right.  Duplicate sets are also
    removed from the union. *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | union ?E1 ?E2 => let Acc1 := go Acc E2 in go Acc1 E1
     | empty => Acc
     | ?E1 => match Acc with
              | empty => E1
              | context [E1] => Acc
              | _ => constr:(union E1 Acc)
              end
     end
  in go empty V.

(** The tactic [(pick fresh Y for L)] takes a finite set of atoms [L]
    and a fresh name [Y], and adds to the context an atom with name
    [Y] and a proof that [(~ In Y L)], i.e., that [Y] is fresh for
    [L].  The tactic will fail if [Y] is already declared in the
    context. *)

Tactic Notation "pick" "lfresh" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (loc_fresh_for_set L) as [Y Fr]).


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
