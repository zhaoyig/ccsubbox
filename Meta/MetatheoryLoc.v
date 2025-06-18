(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

Require Import Coq.Arith.Arith.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.

Require Import Coq.FSets.FSets.
Require Import CoqListFacts.
Require Import FSetExtra.
Require Import FSetWeakNotin.
Require Import LibTactics.

Require Import Lia.

(* ********************************************************************** *)
(** * Defining locs *)

(** Locs are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on locs is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of locs. *)

Module Type LOC <: UsualDecidableType.

  Parameter loc : Set.
  Definition t := loc.

  Parameter eq_dec : forall x y : loc, {x = y} + {x <> y}.

  Parameter loc_fresh_for_list :
    forall (xs : list t), {x : loc | ~ List.In x xs}.

  Parameter fresh : list loc -> loc.

  Parameter fresh_not_in : forall l, ~ In (fresh l) l.

  Parameter nat_of : loc -> nat.

  #[global]
  Hint Resolve eq_dec : core.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End LOC.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module Loc : LOC.

  (* begin hide *)
  Definition loc := nat.
  Definition t := loc.

  Definition eq_dec := eq_nat_dec.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y. auto with arith.
      simpl. induction z. lia. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, List.In x xs -> x <= n }.
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
    exists (S x). intros J. lapply (H (S x)). lia. trivial.
  Qed.

  Definition fresh (l : list loc) :=
    match loc_fresh_for_list l with
      (exist _ x _) => x
    end.

  Lemma fresh_not_in : forall l, ~ In (fresh l) l.
  Proof.
    intro l. unfold fresh.
    destruct loc_fresh_for_list. auto.
  Qed.

  Definition nat_of := fun (x : loc) => x.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  (* end hide *)

End Loc.

(** We make [loc], [fresh], [fresh_not_in] and [loc_fresh_for_list] available
    without qualification. *)

Notation loc := Loc.loc.
Notation fresh := Loc.fresh.
Notation fresh_not_in := Loc.fresh_not_in.
Notation loc_fresh_for_list := Loc.loc_fresh_for_list.

(* Automatically unfold Loc.eq *)
Global Arguments Loc.eq /.

(** It is trivial to declare an instance of [EqDec] for [loc]. *)

#[export] Instance EqDec_loc : @EqDec loc eq eq_equivalence.
Proof. exact Loc.eq_dec. Defined.


(* ********************************************************************** *)
(** * Finite sets of locs *)

(** We use our implementation of locs to obtain an implementation of
    finite sets of locs.  We give the resulting type an intuitive
    name, as well as import names of set operations for use within
    this library.  In order to avoid polluting Coq's namespace, we do
    not use [Module Export]. *)

Module Import LocSetImpl : FSetExtra.WSfun Loc :=
  FSetExtra.Make Loc.

Notation locs :=
  LocSetImpl.t.

(** The [LocSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of locs. *)


Module Export LocSetDecide := Coq.FSets.FSetDecide.WDecide_fun Loc LocSetImpl.

(** The [LocSetNotin] module provides the [destruct_notin] and
    [solve_notin] for reasoning about non-membership in finite sets of
    locs, as well as a variety of lemmas about non-membership. *)

Module Export LocSetNotin := FSetWeakNotin.Notin_fun Loc LocSetImpl.

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module LocSetFacts := FSetFacts.WFacts_fun Loc LocSetImpl.
Module LocSetProperties := FSetProperties.WProperties_fun Loc LocSetImpl.

Export LocSetFacts.

(* ********************************************************************** *)
(** * Properties *)

(** For any given finite set of locs, we can generate an loc fresh
    for it. *)

Lemma loc_fresh : forall L : locs, { x : loc | ~ In x L }.
Proof.
  intros L. destruct (loc_fresh_for_list (elements L)) as [a H].
  exists a. intros J. contradiction H.
  rewrite <- CoqListFacts.InA_iff_In. auto using elements_1.
Qed.


(* ********************************************************************** *)
(** * Tactic support for picking fresh locs *)

(* begin hide *)

(** The auxiliary tactic [simplify_list_of_loc_sets] takes a list of
    finite sets of locs and unions everything together, returning the
    resulting single finite set. *)

Ltac simplify_list_of_loc_sets L :=
  let L := eval simpl in L in
  let L := ltac_remove_dups L in
  let L := eval simpl in (List.fold_right union empty L) in
  match L with
    | context C [union ?E empty] => context C [ E ]
  end.

(* end hide *)

(** [gather_locs_with F] returns the union of all the finite sets
    [F x] where [x] is a variable from the context such that [F x]
    type checks. *)

Ltac gather_locs_with F :=
  let apply_arg x :=
    match type of F with
      | _ -> _ -> _ -> _ => constr:(@F _ _ x)
      | _ -> _ -> _ => constr:(@F _ x)
      | _ -> _ => constr:(@F x)
    end in
  let rec gather V :=
    match goal with
      | H : _ |- _ =>
        let FH := apply_arg H in
        match V with
          | context [FH] => fail 1
          | _ => gather (union FH V)
        end
      | _ => V
    end in
  let L := gather empty in eval simpl in L.

(** [beautify_fset V] assumes that [V] is built as a union of finite
    sets and returns the same set cleaned up: empty sets are removed
    and items are laid out in a nicely parenthesized way. *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | union ?E1 ?E2 => let Acc2 := go Acc E2 in go Acc2 E1
     | empty => Acc
     | ?E1 => match Acc with
                | empty => E1
                | _ => constr:(union E1 Acc)
              end
     end
  in go empty V.

(** The tactic [pick fresh Y for L] takes a finite set of locs [L]
    and a fresh name [Y], and adds to the context an loc with name
    [Y] and a proof that [~ In Y L], i.e., that [Y] is fresh for [L].
    The tactic will fail if [Y] is already declared in the context.

    The variant [pick fresh Y] is similar, except that [Y] is fresh
    for "all locs in the context."  This version depends on the
    tactic [gather_locs], which is responsible for returning the set
    of "all locs in the context."  By default, it returns the empty
    set, but users are free (and expected) to redefine it. *)

Ltac gather_locs :=
  constr:(empty).

Tactic Notation "pick" "lfresh" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (loc_fresh L) as [Y Fr]).

Tactic Notation "pick" "lfresh" ident(Y) :=
  let L := gather_locs in
  pick lfresh Y for L.

Ltac pick_lfresh y :=
  pick lfresh y.

(** Example: We can redefine [gather_locs] to return all the
    "obvious" locs in the context using the [gather_locs_with] thus
    giving us a "useful" version of the "[pick lfresh]" tactic. *)

Ltac gather_locs ::=
  let A := gather_locs_with (fun x : locs => x) in
  let B := gather_locs_with (fun x : loc => singleton x) in
  constr:(union A B).

Lemma example_pick_lfresh_use : forall (x y z : loc) (L1 L2 L3: locs), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3.
  pick_lfresh k.

  (** At this point in the proof, we have a new loc [k] and a
      hypothesis [Fr] that [k] is fresh for [x], [y], [z], [L1], [L2],
      and [L3]. *)

  trivial.
Qed.
(* end show *)
