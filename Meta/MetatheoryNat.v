Require Import Coq.Arith.Arith.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.

Require Import Coq.FSets.FSets.
Require Import CoqListFacts.
Require Import FSetExtra.
Require Import FSetWeakNotin.
Require Import LibTactics.

Require Import List.
(* Require Import Max. *)
Require Import OrderedTypeEx.
Require Import OrderedType.

Require Import FSetDecide.
Require Import FSetFacts.

(** Helpers, defining a set of natural numbers. *)
Module Type NATSET <: UsualDecidableType.
    Definition t := nat.
    (* Declare Module OT : UsualOrderedType with Definition t := nat. *)
    Parameter eq_dec : forall x y : nat, {x = y} + {x <> y}.

    #[global]
    Hint Resolve eq_dec : core.

    Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.
End NATSET.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module NatSet : NATSET.
    (* begin hide *)
    Definition t := nat.
    Module OT := Nat_as_OT.
    Module Facts := OrderedTypeFacts OT.
    Definition eq_dec : forall x y : nat, {x = y} + {x <> y} := 
        Facts.eq_dec. 

    Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.
  (* end hide *)
End NatSet.

(** Defining a set of Natural Numbers. *)
Module NatSetImpl : FSetExtra.WSfun NatSet :=
  FSetExtra.Make NatSet.

(** The type [nats] is the type of finite sets of [nat]s. *)
Notation nats := NatSetImpl.t.
Notation "{}N" :=
  NatSetImpl.empty : metatheory_scope.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of atoms. *)

Module NatSetDecide := Coq.FSets.FSetDecide.WDecide_fun NatSet NatSetImpl.
Module NatSetNotin  := FSetWeakNotin.Notin_fun   NatSet NatSetImpl.
Module NatSetFacts  := FSetFacts.WFacts_fun NatSet NatSetImpl.
Module NatSetProperties := FSetProperties.WProperties_fun NatSet NatSetImpl.

