(** Support here for Capture Sets, a.k.a a record
    of free and bound variables tracking which variables
    are captured by a particualar type. *)

Require Import Metatheory.
Require Import Tactics.
Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FSetFacts.
Require Import Atom.

(** Helpers, defining a set of natural numbers. *)
Module Type NATSET.
  Declare Module OT : UsualOrderedType with Definition t := nat.
  Parameter eq_nat_dec : forall x y : nat, {x = y} + {x <> y}.
End NATSET.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module NatSetImpl : NATSET.
  (* begin hide *)
  Module OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts OT.
  Definition eq_nat_dec : forall x y : nat, {x = y} + {x <> y} :=
    Facts.eq_dec. 
  (* end hide *)
End NatSetImpl.

(** Defining a set of Natural Numbers. *)
Module NatSet : FiniteSets.S with Module E := NatSetImpl.OT :=
  FiniteSets.Make NatSetImpl.OT.

(** The type [nats] is the type of finite sets of [nat]s. *)
Notation nats := NatSet.F.t.
Notation "{}N" :=
  NatSet.F.empty : metatheory_scope.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of atoms. *)

Module NatSetDecide := FSetDecide.Decide NatSet.F.
Module NatSetNotin  := FSetNotin.Notin   NatSet.F.
Module NatSetFacts  := FSetFacts.Facts NatSet.F.

(* *********************************************************************** *)
(** ** Tactics for working with finite sets of nats *)

(** The tactic [fnsetdec] is a general purpose decision procedure
    for solving facts about finite sets of atoms. *)

Ltac fnsetdec := try apply NatSet.eq_if_Equal; NatSetDecide.fsetdec.

(** The tactic [notin_simpl] simplifies all hypotheses of the form [(~
    In x F)], where [F] is constructed from the empty set, singleton
    sets, and unions. *)

Ltac nnotin_simpl := NatSetNotin.notin_simpl_hyps.

(** The tactic [notin_solve], solves goals of the form [(~ In x F)],
    where [F] is constructed from the empty set, singleton sets, and
    unions.  The goal must be provable from hypothesis of the form
    simplified by [notin_simpl]. *)

Ltac nnotin_solve := NatSetNotin.notin_solve.

(** A captureset -- a pair of free variables and bound variables. *)
Inductive captureset : Type :=
  | cset_universal : captureset
  | cset_set : atoms -> nats -> captureset.

Definition empty_cset := cset_set {} {}N.
Definition universal_cset := cset_universal.

(** The empty set may be written similarly to informal practice. *)
Notation "{}C" :=
  empty_cset : metatheory_scope.
Notation "{*}C" :=
  universal_cset : metatheory_scope.

(** Accessors *)
Definition cset_fvar (c : captureset) : atoms :=
  match c with
  | cset_universal => {}
  | cset_set A N => A
  end.
Definition cset_bvar (c : captureset) : nats :=
  match c with
  | cset_universal => {}N
  | cset_set A N => N
  end.

(** Singletons *)
Definition cset_singleton_fvar (a : atom) :=
  (cset_set (AtomSet.F.singleton a) (NatSet.F.empty)).
Definition cset_singleton_bvar (k : nat) :=
  (cset_set (AtomSet.F.empty) (NatSet.F.singleton k)).

(** Predicates for determining if a capture set explicity references
    a variable -- used for determining if a capture set is well formed.
    Don't use these predicates for determining if a capture set
    captures a variable, as one needs to also test cset_universal. *)
Definition cset_references_bvar (k : nat) (c : captureset) :=
  NatSet.F.In k (cset_bvar c).
Definition cset_references_fvar (a : atom) (c : captureset) :=
  AtomSet.F.In a (cset_fvar c).
Definition cset_references_bvar_dec (k : nat) (c : captureset) :=
  NatSet.F.mem k (cset_bvar c).
Definition cset_references_fvar_dec (a : atom) (c : captureset) :=
  AtomSet.F.mem a (cset_fvar c).

Lemma cset_references_bvar_eq (k : nat) (c : captureset) :
  cset_references_bvar_dec k c = true <-> cset_references_bvar k c.
Proof.
  unfold cset_references_bvar_dec. unfold cset_references_bvar.
  rewrite <-NatSetFacts.mem_iff. intuition.
Qed.

Lemma cset_references_fvar_eq (k : atom) (c : captureset) :
  cset_references_fvar_dec k c = true <-> cset_references_fvar k c.
Proof.
  unfold cset_references_fvar_dec. unfold cset_references_bvar.
  rewrite <-AtomSetFacts.mem_iff. intuition.
Qed.

Lemma cset_not_references_bvar_eq (k : nat) (c : captureset) :
  cset_references_bvar_dec k c = false <-> ~ cset_references_bvar k c.
Proof.
  unfold cset_references_bvar_dec. unfold cset_references_bvar.
  rewrite <-NatSetFacts.not_mem_iff. intuition.
Qed.

Lemma cset_not_references_fvar_eq (k : atom) (c : captureset) :
  cset_references_fvar_dec k c = false <-> ~ cset_references_fvar k c.
Proof.
  unfold cset_references_fvar_dec. unfold cset_references_bvar.
  rewrite <-AtomSetFacts.not_mem_iff. intuition.
Qed.


(** More predicates *)
Definition empty_cset_bvar_references (c : captureset) : Prop :=
  NatSet.F.Empty (cset_bvar c).
Definition empty_cset_fvar_references (c : captureset) : Prop :=
  AtomSet.F.Empty (cset_fvar c).


(** Capture set unions are what you'd expect. *)
Definition cset_union (c1 c2 : captureset) : captureset :=
  match c1 , c2 with
  | _ , cset_universal => cset_universal
  | cset_universal , _ => cset_universal
  | cset_set A1 N1 , cset_set A2 N2 => cset_set (AtomSet.F.union A1 A2) (NatSet.F.union N1 N2)
  end.

(** Empty capture sets / universal capture sets *)
Definition cset_empty (c : captureset) : Prop :=
  match c with
  | cset_universal => False
  | cset_set A N => empty_cset_bvar_references c /\ empty_cset_fvar_references c
  end.

Definition cset_remove_bvar (k : nat) (c : captureset) : captureset :=
  match c with
  | cset_universal => cset_universal
  | cset_set AC NC => cset_set AC (NatSet.F.remove k NC)
  end.

Definition cset_remove_fvar (a : atom) (c : captureset) : captureset :=
  match c with
  | cset_universal => cset_universal
  | cset_set AC NC => cset_set (AtomSet.F.remove a AC) NC
  end.

(** Opening a capture set with a bound variable d[k -> c] *)
Definition open_captureset_bvar (k : nat) (c : captureset) (d : captureset) : captureset :=
  if cset_references_bvar_dec k d then 
    cset_union c (cset_remove_bvar k d)
  else 
    d.

(** Substituting a capture set with a free variable d[a -> c] *)
Definition substitute_captureset_fvar (a : atom) (c : captureset) (d: captureset) : captureset :=
  if cset_references_fvar_dec a d then
    cset_union c (cset_remove_fvar a d)
  else
    d.

(* TODO rename to cset_subset *)
(** Predicates around subsets, and decidability for destruction *)
Inductive cset_subset_prop : captureset -> captureset -> Prop :=
| cset_subset_univ : forall c, cset_subset_prop c cset_universal
| cset_subset_elem : forall ac nc ad nd,  
  AtomSet.F.Subset ac ad -> NatSet.F.Subset nc nd -> cset_subset_prop (cset_set ac nc) (cset_set ad nd)
.
      
Definition cset_subset_dec (c d : captureset) :=
  match c , d with
  | _ , cset_universal => true
  | cset_universal , _ => false
  | cset_set AC NC , cset_set AD ND => AtomSet.F.subset AC AD && NatSet.F.subset NC ND  
  end.

(** A helper, to eliminate terms like <complex computation> && false *)
Local Lemma reduce_false (b : bool) : b && false = false.
Proof.
destr_bool.
Qed.

(** Why isn't this part of the standard library? **)
Local Lemma eliminate_false (b : bool) : (b = false) <-> (b <> true).
Proof.
destr_bool; split; destr_bool.
contradict H; trivial.
Qed.

(** Two relations relating the subset relation to the subset computation. *)
Lemma cset_subset_iff (c1 c2 : captureset) : cset_subset_prop c1 c2 <-> cset_subset_dec c1 c2 = true.
Proof.
  split.
  (* --> *)
  * intro. inversion H ; unfold cset_subset_dec.
    - subst. destruct c1 ; eauto.
    - subst. 
      rewrite NatSetFacts.subset_iff in *. rewrite AtomSetFacts.subset_iff in *. 
      rewrite H0. rewrite H1. auto.
  (* <-- *)
  * intro. unfold cset_subset_dec in H.
    destruct c1 eqn:H1 ; destruct c2 eqn:H2.
    - apply cset_subset_univ.
    - discriminate H.
    - apply cset_subset_univ.
    - apply cset_subset_elem ; rewrite andb_true_iff in H ; destruct H ;
      rewrite <- NatSetFacts.subset_iff in * ; rewrite <- AtomSetFacts.subset_iff in * ; auto.
Qed.

Lemma cset_subset_not_iff (c1 c2 : captureset) : ~ cset_subset_prop c1 c2 <-> cset_subset_dec c1 c2 = false.
Proof with auto*.
  split.
  * intro H. rewrite eliminate_false. contradict H. apply cset_subset_iff...
  * intro H. rewrite eliminate_false in H. contradict H. apply cset_subset_iff...
Qed.
