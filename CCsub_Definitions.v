Require Export TaktikZ.
Require Export Signatures.
Require Export Metatheory.
Require Export CaptureSets.
Require Import Coq.Program.Wf.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

(** We use a locally nameless representation for Fsub, where bound
    variables are represented as natural numbers (de Bruijn indices)
    and free variables are represented as [atom]s.  The type [atom],
    defined in the [Atom] library, represents names: there are
    infinitely many atoms, equality is decidable on atoms, and it is
    possible to generate an atom fresh for any given finite set of
    atoms.

    We say that the definitions below define pre-types ([typ]) and
    pre-expressions ([exp]), collectively pre-terms, since the
    datatypes admit terms, such as [(typ_all typ_top (typ_bvar 3))],
    where indices are unbound.  A term is locally closed when it
    contains no unbound indices.

    Note that indices for bound type variables are distinct from
    indices for bound expression variables.  We make this explicit in
    the definitions below of the opening operations. *)
Inductive typ : Type :=
  (* C P *)
  | typ_capt : cap -> pretyp -> typ
  (* X *)
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
with pretyp : Type :=
  | typ_top : pretyp
  | typ_arrow : typ -> typ -> pretyp
  | typ_all : typ -> typ -> pretyp
  (** non-local returns: handlers need to be annotated with their return value *)
  | typ_ret : typ -> pretyp
  .


Inductive exp : Type :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  (** handle [Targ] { handler => exp }
      for non-local returns. *)
  | exp_handle : typ -> exp -> exp
  (** throw[exp_1/handler] exp_2 *)
  | exp_do_ret : exp -> exp -> exp
  (** label -- generated at runtime *)
  | exp_lvar : label -> exp
.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.

(* Coercion cset_bvar : nat >-> cap. *)
(* Coercion cset_fvar : atom >-> cap. *)

(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.

    The notation used below for decidable equality on atoms and
    natural numbers (e.g., [K === J]) is defined in the [Metatheory]
    library.  The order of arguments to each "open" function is the
    same.  For example, [(open_tt_rec K U T)] can be read as
    "substitute [U] for index [K] in [T]."

    Note that we assume that [U] is locally closed (and similarly for
    the other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Definition cv (T : typ) : cap :=
  match T with
  | typ_bvar n => {}      (* TODO is there a better way to do this? *)
  | typ_fvar x => `cset_fvar` x
  | typ_capt C _ => C
  end.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar J => if K === J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_capt C P => typ_capt (open_cset K (cv U) C) (open_tpt_rec K U P)
  end
with open_tpt_rec (K : nat) (U : typ) (T : pretyp)  {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_ret T1 => typ_ret (open_tt_rec K U T1)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_handle Targ e1 => exp_handle (open_tt_rec K U Targ) (open_te_rec (S K) U e1)
  | exp_do_ret e1 e2 => exp_do_ret (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_lvar a => exp_lvar a
  end.

Fixpoint open_ct_rec (k : nat) (c : cap) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar i => typ_bvar i
  | typ_fvar x => typ_fvar x
  | typ_capt C P => typ_capt (open_cset k c C) (open_cpt_rec k c P)
  end
with open_cpt_rec (k : nat) (c : cap) (T : pretyp)  {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  | typ_all T1 T2 => typ_all (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  | typ_ret T1 => typ_ret (open_ct_rec k c T1)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (c : cap) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k === i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs t e1 => exp_abs (open_ct_rec k c t) (open_ee_rec (S k) f c e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f c e1) (open_ee_rec k f c e2)
  | exp_tabs t e1 => exp_tabs (open_ct_rec k c t) (open_ee_rec (S k) f c e1)
  | exp_tapp e1 t => exp_tapp (open_ee_rec k f c e1) (open_ct_rec k c t)
  | exp_handle Targ e1 => exp_handle (open_ct_rec k c Targ) (open_ee_rec (S k) f c e1)
  | exp_do_ret e1 e2 => exp_do_ret (open_ee_rec k f c e1) (open_ee_rec k f c e2)
  | exp_lvar a => exp_lvar a
  end.


(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_tpt T U := open_tpt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 c := open_ee_rec 0 e2 c e1.
Definition open_ct T c := open_ct_rec 0 c T.
Definition open_cpt T c := open_cpt_rec 0 c T.

(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed we much
    check that [T1] is locally closed, and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2)
>>  or we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2)
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite
    quantification": we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_capt : forall C P,
      capt C ->
      pretype P ->
      type (typ_capt C P)
with pretype : pretyp -> Prop :=
  | type_top : pretype typ_top
  | type_arrow : forall L T1 T2,
    type T1 ->
    (forall X : atom, X `notin` L -> type (open_ct T2 (`cset_fvar` X))) ->
    pretype (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
    type T1 ->
    (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
    pretype (typ_all T1 T2)
  | type_exc : forall T1,
    type T1 ->
    pretype (typ_ret T1)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x (`cset_fvar` x))) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_try : forall L Targ e1,
      type Targ ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x (`cset_fvar` x))) ->
      expr (exp_handle Targ e1)
  | expr_throw : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_do_ret e1 e2)
  | expr_handler : forall a,
      expr (exp_lvar a)
  .


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The [Metatheory] and [Environment] libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  The [Environment] library treats environments
    as lists of type [list (atom * A)].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive binding : Type :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

Inductive signature : Type :=
  | bind_sig : typ -> signature.

(** A binding [(X, bind_sub T)] records that a type variable [X] is a
    subtype of [T], and a binding [(x, bind_typ U)] records that an
    expression variable [x] has type [U].

    We define an abbreviation [env] for the type of environments, and
    an abbreviation [empty] for the empty environment.

    Note: Each instance of [Notation] below defines an abbreviation
    since the left-hand side consists of a single identifier that is
    not in quotes.  These abbreviations are used for both parsing (the
    left-hand side is equivalent to the right-hand side in all
    contexts) and printing (the right-hand side is pretty-printed as
    the left-hand side).  Since [nil] is normally a polymorphic
    constructor whose type argument is implicit, we prefix the name
    with "[@]" to signal to Coq that we are going to supply arguments
    to [nil] explicitly. *)

Notation env := (list (atom * binding)).
Notation sig := (list (label * signature)).
Notation empty := (@nil (atom * binding)).

(** We also define a notation that makes it convenient to write one
    element lists.  This notation is useful because of our convention
    for building environments; see the examples below. *)

Notation "[ x ]" := (x :: nil).

(** #<b>#Examples:#</b># We use a convention where environments are
    never built using a cons operation [((x, a) :: E)] where [E] is
    non-[nil].  This makes the shape of environments more uniform and
    saves us from excessive fiddling with the shapes of environments.
    For example, Coq's tactics sometimes distinguish between consing
    on a new binding and prepending a one element list, even though
    the two operations are convertible with each other.

    Consider the following environments written in informal notation.
<<
  1. (empty environment)
  2. x : T
  3. x : T, Y <: S
  4. E, x : T, F
>>  In the third example, we have an environment that binds an
    expression variable [x] to [T] and a type variable [Y] to [S].
    In Coq, we would write these environments as follows.
<<
  1. empty
  2. [(x, bind_typ T)]
  3. [(Y, bind_sub S)] ++ [(x, bind_typ T)]
  4. F ++ [(x, bind_typ T)] ++ E
>> The symbol "[++]" denotes list concatenation and associates to the
    right.  (That notation is defined in Coq's [List] library.)  Note
    that in Coq, environments grow on the left, since that is where
    the head of a list is. *)


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(** A type [T] is well-formed with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    Note: It is tempting to define the premise of [wf_typ_var] as [(X
    `in` dom E)], since that makes the rule easier to apply (no need
    to guess an instantiation for [U]).  Unfortunately, this is
    incorrect.  We need to check that [X] is bound as a type-variable,
    not an expression-variable; [(dom E)] does not distinguish between
    the two kinds of bindings. *)

(** For our current calculus, we disallow type variables from showing up in capture
  sets -- only term variables are allowed. *)
Inductive bound (x : atom) (T : typ) (E : env) : Prop :=
  | bound_typ :
    binds x (bind_typ T) E ->
    bound x T E
  | bound_sub :
    binds x (bind_sub T) E ->
    bound x T E.

Definition allbound (E : env) (xs : atoms) : Prop :=
  forall x, x `in`A xs -> exists T, bound x T E.

Inductive wf_cset : env -> atoms -> cap -> Prop :=
  | wf_concrete_cset : forall E A xs b ls,
    allbound E xs ->
    xs `c`A A ->
    wf_cset E A (cset_set xs {}N b ls)
.

Definition wf_cset_in (E : env) (C : cap) : Prop :=
  wf_cset E (dom E) C.

(* Wellformedness of types where locally bound variables are only
   allowed in positive positions. *)
Inductive wf_typ : env -> atoms -> atoms -> typ -> Prop :=
  | wf_typ_var : forall U E Ap Am (X : atom),
      binds X (bind_sub U) E ->
      X `in`A Ap ->
      wf_typ E Ap Am (typ_fvar X)
  | wf_typ_capt : forall E Ap Am C P,
      wf_cset E Ap C ->
      wf_pretyp E Ap Am P ->
      wf_typ E Ap Am (typ_capt C P)
with wf_pretyp : env -> atoms -> atoms -> pretyp -> Prop :=
  | wf_typ_top : forall E Ap Am,
      wf_pretyp E Ap Am typ_top
  | wf_typ_arrow : forall L E Ap Am T1 T2,
      wf_typ E Am Ap T1 ->
      (forall X : atom, X `notin` L ->
                   wf_typ ([(X, bind_typ T1)] ++ E)
                          (Ap `union` singleton X)
                          Am
                          (open_ct T2 (`cset_fvar` X))) ->
      wf_pretyp E Ap Am (typ_arrow T1 T2)
  | wf_typ_all : forall L E Ap Am T1 T2,
      wf_typ E Am Ap T1 ->
      (forall X : atom, X `notin` L ->
                   wf_typ ([(X, bind_sub T1)] ++ E)
                          (Ap `u`A {X}A)
                          (Am `u`A {X}A) (open_tt T2 X)) ->
      wf_pretyp E Ap Am (typ_all T1 T2)
  | wf_typ_ret : forall E Ap Am T,
      wf_typ E Ap Am T ->
      wf_pretyp E Am Ap (typ_ret T)
  .

Definition wf_typ_in (E : env) (T : typ) : Prop :=
  wf_typ E (dom E) (dom E) T.

Definition wf_pretyp_in (E : env) (U : pretyp) : Prop :=
  wf_pretyp E (dom E) (dom E) U.

Hint Unfold wf_typ_in : core.
Hint Unfold wf_pretyp_in : core.

(** An environment E is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [ok]
    relation defined in the [Environment] library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ_in E T ->
      X `notin` dom E ->
      wf_env ([(X, bind_sub T)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ_in E T ->
      x `notin` dom E ->
      wf_env ([(x, bind_typ T)] ++ E).

Inductive wf_sig : sig -> Prop :=
| wf_sig_empty :
    wf_sig nil
| wf_sig_typ : forall (E : sig) (x : label) (T : typ),
    wf_sig E ->
    wf_typ_in empty T ->
    ~ LabelSet.F.In x (Signatures.dom E) ->
    wf_sig ([(x, bind_sig T)] ++ E).


(** The definition of "fv" used in typing jdmgnts*)
Fixpoint free_for_cv (e : exp) : cap :=
match e with
  | exp_bvar i => {}
  | exp_fvar x => (`cset_fvar` x)
  | exp_abs t e1 => (free_for_cv e1)
  | exp_app e1 e2 => (cset_union (free_for_cv e1) (free_for_cv e2))
  | exp_tabs t e1 => (free_for_cv e1)
  | exp_tapp e1 t => (free_for_cv e1)
  | exp_handle Targ e1 => (free_for_cv e1)
  | exp_do_ret e1 e2 => (cset_union (free_for_cv e1) (free_for_cv e2))
  | exp_lvar x => (`cset_lvar` x) (** this is crucial! *)
  end.

(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

Reserved Notation "E |-sc C <: D" (at level 70, C at next level).
Inductive subcapt : env -> cap -> cap -> Prop :=
  | subcapt_universal : forall E C xs ls,
      wf_cset_in E (cset_set xs {}N true ls) ->
      wf_cset_in E C ->
      E |-sc C <: (cset_set xs {}N true ls)

  | subcapt_in_fvar : forall E x xs b ls,
      wf_cset_in E (`cset_fvar` x) ->
      wf_cset_in E (cset_set xs {}N b ls) ->
      x `in` xs ->
      E |-sc (`cset_fvar` x) <: (cset_set xs {}N b ls)
  | subcapt_in_lvar : forall E l xs b ls,
      wf_cset_in E (`cset_lvar` l) ->
      wf_cset_in E (cset_set xs {}N b ls) ->
      l `in`L ls ->
      E |-sc (`cset_lvar` l) <: (cset_set xs {}N b ls)

  | subcapt_in_univ : forall E D,
      wf_cset_in E D ->
      `* in` D ->
      E |-sc {*} <: D
  | subcapt_var : forall E x T C,
      binds x (bind_typ T) E ->
      E |-sc (cv T) <: C ->
      E |-sc (`cset_fvar` x) <: C
  | subcapt_tvar : forall E x T C,
      binds x (bind_sub T) E ->
      E |-sc (cv T) <: C ->
      E |-sc (`cset_fvar` x) <: C
  | subcapt_set : forall E xs b ls D,
      wf_cset_in E D ->
      AtomSet.F.For_all (fun x => E |-sc (`cset_fvar` x) <: D) xs ->
      LabelSet.F.For_all (fun l => E |-sc (`cset_lvar` l) <: D) ls ->
      implb b (`* mem` D) = true ->
      E |-sc (cset_set xs {}N b ls) <: D
  where "E |-sc C <: D" := (subcapt E C D).

(** The definition of subtyping is straightforward.  It uses the
    [binds] relation from the [Environment] library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Reserved Notation "E |-s S <: T" (at level 70, S at next level).
Reserved Notation "E |-sp S <: T" (at level 70, S at next level).

Inductive sub : env -> typ -> typ -> Prop :=

  (* Instead of having rules for refl and trans, the original Fsub calculus special cases
     those rules to type variables. Refl and Trans are then defined externally in sub_reflexivity
     and sub_transitivity. *)
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ_in E (typ_fvar X) ->
      E |-s (typ_fvar X) <: (typ_fvar X)

  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      E |-s U <: T ->
      E |-s (typ_fvar X) <: T

  | sub_capt : forall E C1 C2 P1 P2,
      E |-sc C1 <: C2 ->
      E |-sp P1 <: P2 ->
      E |-s (typ_capt C1 P1) <: (typ_capt C2 P2)

  where "E |-s S <: T" := (sub E S T)

with sub_pre : env -> pretyp -> pretyp -> Prop :=
  (*
      cv(S, E) = {}
      -------------
      E ⊢ S <: ⊤
  *)
  | sub_top : forall E S,
      wf_env E ->
      wf_pretyp_in E S ->
      E |-sp S <: typ_top

  (*
      E ⊢ T₁ <: S₁    E, x: T₁ ⊢ S₂ <: T₂
      ------------------------------------
          E ⊢ ∀(x: S₁)S₂ <: ∀(x: T₁)T₂

      New: Here we open S2 and T2 with x
  *)
  | sub_arrow : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      wf_typ_in E T1 ->
      wf_typ_in E S1 ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x))) ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ S1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct S2 (`cset_fvar` x))) ->
      (forall x : atom, x `notin` L ->
          ([(x, bind_typ T1)] ++ E) |-s (open_ct S2 (`cset_fvar` x)) <: (open_ct T2 (`cset_fvar` x))) ->
      E |-sp (typ_arrow S1 S2) <: (typ_arrow T1 T2)

  (*
      E ⊢ T₁ <: S₁    E, X<:T₁ ⊢ S₂ <: T₂
      ------------------------------------
        E ⊢ ∀[X<:S₁]S₂ <: ∀[X<:T₁]T₂
  *)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      wf_typ_in E T1 ->
      wf_typ_in E S1 ->
      (forall X : atom, X `notin` L ->
          wf_typ ([(X, bind_sub T1)] ++ E) (dom E `u`A {X}A) (dom E `u`A {X}A) (open_tt T2 X)) ->
      (forall X : atom, X `notin` L ->
          wf_typ ([(X, bind_sub S1)] ++ E) (dom E `u`A {X}A) (dom E `u`A {X}A) (open_tt S2 X)) ->
      (forall X : atom, X `notin` L ->
          ([(X, bind_sub T1)] ++ E) |-s (open_tt S2 X) <: (open_tt T2 X)) ->
      E |-sp (typ_all S1 S2) <: (typ_all T1 T2)

  | sub_ret : forall E T1 T2,
      E |-s T2 <: T1 ->
      E |-sp (typ_ret T1) <: (typ_ret T2)

  where "E |-sp S <: T" := (sub_pre E S T).


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

Reserved Notation "E @ Q |-t e ~: T" (at level 70, Q at next level, e at next level).
Inductive typing : env -> sig -> exp -> typ -> Prop :=
  | typing_var_tvar : forall E Q x X,
      wf_env E ->
      wf_sig Q ->
      binds x (bind_typ (typ_fvar X)) E ->
      E @ Q |-t (exp_fvar x) ~: (typ_fvar X)
  | typing_var : forall E Q x C P,
      wf_env E ->
      wf_sig Q ->
      binds x (bind_typ (typ_capt C P)) E ->
      E @ Q |-t (exp_fvar x) ~: (typ_capt (`cset_fvar` x) P)
  | typing_abs : forall L E Q V e1 T1,
      wf_typ_in E V ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ V)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T1 (`cset_fvar` x))) ->
      (forall x : atom, x `notin` L ->
        ([(x, bind_typ V)] ++ E) @ Q |-t (open_ee e1 x (`cset_fvar` x)) ~: (open_ct T1 (`cset_fvar` x))) ->
      E @ Q  |-t (exp_abs V e1) ~: (typ_capt (free_for_cv e1) (typ_arrow V T1))
  | typing_app : forall T1 E Q e1 e2 T2 Cf T1',
      E @ Q |-t e1 ~: (typ_capt Cf (typ_arrow T1 T2)) ->
      E @ Q |-t e2 ~: T1' -> (** typing E e2 T1 *)
      E |-s T1' <: T1 -> (** e : S', S' <: S, f : S -> T |- f e : T[x |- cv(S')] *)
      E @ Q |-t (exp_app e1 e2) ~: (open_ct T2 (cv T1'))
  | typing_tabs : forall L E Q V e1 T1,
      wf_typ_in E V ->
      (forall x : atom, x `notin` L ->
        wf_typ ([(x, bind_sub V)] ++ E) (dom E `u`A {x}A) (dom E `u`A {x}A) (open_tt T1 x)) ->
      (forall X : atom, X `notin` L ->
        ([(X, bind_sub V)] ++ E) @ Q |-t (open_te e1 X) ~: (open_tt T1 X)) ->
      E @ Q |-t (exp_tabs V e1) ~: (typ_capt (free_for_cv e1) (typ_all V T1))
  | typing_tapp : forall T1 E Q e1 T T2 C,
      E @ Q |-t e1 ~: (typ_capt C (typ_all T1 T2)) ->
      E |-s T <: T1 ->
      E @ Q |-t (exp_tapp e1 T) ~: (open_tt T2 T)
  | typing_sub : forall S E Q e T,
      E @ Q |-t e ~: S ->
      E |-s S <: T ->
      E @ Q |-t e ~: T

  | typing_handle : forall L E Q T1 e,
      (forall x : atom, x `notin` L ->
        ([(x, bind_typ (typ_capt {*} (typ_ret T1)))] ++ E) @ Q |-t (open_ee e x (`cset_fvar` x)) ~: T1) ->
      E @ Q |-t (exp_handle T1 e) ~: T1

  | typing_do_ret : forall E Q C T1 T2 e1 e2,
      E @ Q |-t e1 ~: (typ_capt C (typ_ret T1)) ->
      E @ Q |-t e2 ~: T1 ->
      E @ Q |-t (exp_do_ret e1 e2) ~: T2

  | typing_lvar : forall E Q C T l,
      wf_env E ->
      wf_sig Q ->
      Signatures.binds l (bind_sig (typ_capt C (typ_ret T))) Q ->
      E @ Q |-t (exp_lvar l) ~: (typ_capt (`cset_lvar` l) (typ_ret T))

  where "E @ Q |-t e ~: T" := (typing E Q e T).


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      expr (exp_tabs T e1) ->
      value (exp_tabs T e1)
  | value_label : forall x,
      value (exp_lvar x)
.


(** ******************************************* **)
(** Stacks / Contexts                           **)
(** ******************************************* **)

Inductive frame : Type :=
  (* [](e) *)
  | KFun : exp -> frame
  (* v([]) *)
  | KArg : exp -> frame  (*(e : exp) -> value e -> frame *)
  (* [] [T] *)
  | KTyp : typ -> frame
  (* try/reset_a [Targ] {exp} *) (** add reset as an expression when we reify continuations *)
  | H : label -> typ -> frame
  (* throw [] (e) *)
  | KThrowHandler : exp -> frame
  (* throw v [] *)
  | KThrowArg : exp -> frame
.

(** We use the following abbreviation to denote runtime stacks *)
Notation ctx := (list frame).

(** the toplevel / empty runtime stack  *)
Notation top := (@nil frame).


(* TODO maybe replace the return type with atoms and specialize this function *)
Fixpoint bound_capabilities (k : ctx) : sig :=
  match k with
  | nil => nil
  | H x T :: k =>  [(x, bind_sig (typ_capt {*} (typ_ret T)))] ++ (bound_capabilities k)
  | _ :: k => bound_capabilities k
  end.

Reserved Notation "E @ Q |-ctx c ~: T" (at level 70, Q at next level, c at next level).

(** IN: env sig ctx*)
Inductive typing_ctx : env -> sig -> ctx -> typ -> Prop :=
  | typing_ctx_empty : forall T Q,
      empty @ Q |-ctx top ~: T

  | typing_ctx_fun : forall E Q C T1 T1' T2 k e,
      E @ Q |-t e ~: T1' ->
      E |-s T1' <: T1 ->
      E @ Q |-ctx k ~: (open_ct T2 (cv T1')) ->
      E @ Q |-ctx KFun e :: k ~: typ_capt C (typ_arrow T1 T2)

  | typing_ctx_arg : forall E Q C T1 T1' T2 k e,
      value e ->
      E @ Q |-t e ~: (typ_capt C (typ_arrow T1 T2)) ->
      E |-s T1' <: T1 ->
      E @ Q |-ctx k ~: (open_ct T2 (cv T1')) ->
      E @ Q |-ctx KArg e :: k ~: T1'

  | typing_ctx_typ : forall E Q C T T1 T2 k,
      E |-s T <: T1 ->
      E @ Q |-ctx k ~: (open_tt T2 T) ->
      E @ Q |-ctx KTyp T :: k ~: (typ_capt C (typ_all T1 T2))

  | typing_ctx_reset : forall E Q a C T k,
      E @ Q |-ctx k ~: T ->
      Signatures.binds a (bind_sig (typ_capt C (typ_ret T))) Q ->
      E @ Q |-ctx H a T :: k ~: T

  | typing_ctx_throw_handler : forall E Q C T Targ k e,
      E @ Q |-ctx k ~: T ->
      (** for exceptions: need to make sure the type on the handler matches
          the current answer type T *)
      E @ Q |-t e ~: Targ ->
      E @ Q |-ctx KThrowHandler e :: k ~: (typ_capt C (typ_ret Targ))

  | typing_ctx_throw_arg : forall E Q C T Targ k e,
      value e ->
      E @ Q |-ctx k ~: T ->
      E @ Q |-t e ~: (typ_capt C (typ_ret Targ)) ->
      E @ Q |-ctx KThrowArg e :: k ~: Targ

  (** TODO: might get stuck at inversion // added to simplify
      proofs around narrowing. *)
  | typing_ctx_sub : forall E Q S T k,
      E @ Q |-ctx k ~: T ->
      sub E S T ->
      E @ Q |-ctx k ~: S

  (*
  | typing_ctx_tvar : forall E T (X : atom) k,
      E |-ctx k ~: T ->
      binds X (bind_sub T) E ->
      E |-ctx k ~: X

    C[t] --> C[v]
    t --> v
    ----------


  | typing_ctx_sub : forall E S T k,
      E |-ctx k ~: T ->
      sub E S T ->
      E |-ctx k ~: S *)

where "E @ Q |-ctx K ~: T" := (typing_ctx E Q K T).


Inductive state : Type :=
  | state_step (e : exp) (c : ctx) (Q : sig) : state
  | state_wind (a : label) (v : exp) (c : ctx) (Q : sig) : state
.

Notation "〈 e | k | Q 〉" := (state_step e k Q ).
Notation "〈throw a # v | k | Q 〉" :=  (state_wind a v k Q).
Reserved Notation "st1 --> st2" (at level 69).

Inductive typing_state : state -> Prop :=
  | typ_step : forall e k T E Q,
      E @ Q |-ctx k ~: T ->
      E @ Q |-t e ~: T ->
      typing_state〈 e | k | Q 〉
  | typ_wind : forall l v k C T Teff E Q,
      E @ Q |-ctx k ~: T ->
      E @ Q |-t v ~: Teff ->
      E @ Q |-t (exp_lvar l) ~: (typ_capt C (typ_ret Teff)) ->
      typing_state〈throw l # v | k | Q 〉
  .

Inductive done : state -> Prop :=
  | done_ret : forall e Q,
      value e ->
      done 〈 e | top | Q 〉
.

(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive step : state -> state -> Prop :=
  | step_app : forall e1 e2 k Q,
      〈 exp_app e1 e2 | k | Q 〉 --> 〈 e1 | KFun e2 :: k | Q 〉

  | step_tapp : forall e T k Q,
      〈 exp_tapp e T | k | Q 〉 --> 〈 e | KTyp T :: k | Q 〉

  | step_pop_app : forall v arg k Q,
      value v ->
      〈 v | KFun arg :: k | Q 〉 --> 〈 arg | KArg v :: k | Q 〉

  | step_throw : forall e1 e2 k Q,
      〈 exp_do_ret e1 e2 | k | Q 〉 --> 〈 e1 | KThrowHandler e2 :: k | Q 〉

  | step_pop_throw : forall v e2 k Q ,
      value v ->
      〈 v | KThrowHandler e2 :: k | Q 〉 --> 〈 e2 | KThrowArg v :: k | Q 〉

  | step_abs : forall v T e k Q,
      value v ->
      〈  v | KArg (exp_abs T e) :: k | Q 〉 --> 〈 (open_ee e v (free_for_cv v)) | k | Q 〉

  | step_tabs : forall T1 T2 e1 k Q,
      〈 exp_tabs T1 e1 | KTyp T2 :: k | Q 〉 --> 〈 (open_te e1 T2) | k | Q 〉

  | step_try : forall T e a k Q,
      a `~in`L Signatures.dom (bound_capabilities k) ->
      〈 exp_handle T e | k | Q 〉-->
                                  〈 open_ee e (exp_lvar a) (`cset_lvar` a)
                                   | H a T :: k
                                   | ([(a, bind_sig (typ_capt {*} (typ_ret T)))]) ++ Q 〉

  (** shifting into unwind *)
  | step_unwind : forall v a k Q,
    value v ->
    〈 v | KThrowArg (exp_lvar a) :: k | Q〉-->
      〈throw a # v | k | Q 〉

  | step_unwind_skip_fun : forall a v e k Q,
    〈throw a # v | KFun e :: k | Q 〉 --> 〈throw a # v | k | Q 〉
  | step_unwind_skip_arg : forall a v e k Q,
    〈throw a # v | KArg e :: k | Q 〉 --> 〈throw a # v | k | Q 〉
  | step_unwind_skip_throw : forall a v e k Q,
    〈throw a # v | KThrowHandler e :: k | Q 〉 --> 〈throw a # v | k | Q 〉
  | step_unwind_skip_throw_arg : forall a v e k Q ,
    〈throw a # v | KThrowArg e :: k | Q 〉 --> 〈throw a # v | k | Q 〉

  | step_unwind_skip_frame : forall a1 v a2 T k Q ,
    a1 <> a2 ->
    〈throw a1 # v | H a2 T :: k | Q 〉--> 〈throw a1 # v | k | Q 〉
  | step_unwind_match_frame : forall a v T k Q,
    〈throw a # v | H a T :: k | Q 〉--> 〈 v | k | Q 〉

where "st1 --> st2" := (step st1 st2).


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

Hint Constructors type pretype expr bound wf_cset wf_typ wf_pretyp wf_env value step sub subcapt typing : core.
Hint Resolve sub_top sub_refl_tvar sub_arrow : core.
Hint Resolve typing_var_tvar typing_var typing_app typing_tapp typing_sub : core.
Hint Unfold wf_typ_in wf_pretyp_in wf_cset_in allbound : core.

Local Ltac cset_unfold_union0 :=
  match goal with
  | _ : _ |- context G [?C `u` (cset_set ?xs ?ns ?us ?ls)] =>
    match C with
    | cset_set _ _ _ _ =>
      rewrite cset_concrete_union
    | C =>
      let HA := match goal with
                | H : wf_cset_in _ C |- _ => H
                | H : wf_cset _ _ C |- _ => H
                | _ =>
                  let H := fresh "WF" in
                  (* NOTE: avoid asserting (wf_cset _ _ C), it takes long to solve. *)
                  assert (wf_cset_in _ C) as HA by eauto; H
                end
      in
      (* Invert, subst and clean up unnecessary hypothesis. *)
      pose proof ltac_mark; inversion HA; subst; clear_until_mark;
      (* Rewrite to avoid matching the same union twice, not sure if necessary. *)
      rewrite cset_concrete_union
    end
  end.

(* We can only define this tactic here, since in CaptureSets we don't have wf_cset. *)
Ltac cset_unfold_union := repeat cset_unfold_union0.

Ltac _csetsimpl_hook ::= cset_unfold_union.

Local Lemma __test_cset_concrete_unfold : forall C xs us ls,
  wf_cset_in nil C ->
  wf_cset_in nil (C `u` (cset_set xs {}N us ls)) ->
  exists xs' us' ls', wf_cset_in nil (cset_set (xs' `u`A xs) {}N (us' || us) ls').
Proof. intros * H; csetsimpl; eauto. Qed.
