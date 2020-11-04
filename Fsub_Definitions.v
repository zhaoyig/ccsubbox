(** Definition of Fsub (System F with subtyping).

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    Table of contents:
      - #<a href="##syntax">Syntax (pre-terms)</a>#
      - #<a href="##open">Opening</a>#
      - #<a href="##lc">Local closure</a>#
      - #<a href="##env">Environments</a>#
      - #<a href="##wf">Well-formedness</a>#
      - #<a href="##sub">Subtyping</a>#
      - #<a href="##typing_doc">Typing</a>#
      - #<a href="##values">Values</a>#
      - #<a href="##reduction">Reduction</a>#
      - #<a href="##auto">Automation</a>#
*)

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
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_capt : captureset -> typ -> typ
.

Inductive exp : Type :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
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
Coercion cset_bvar : nat >-> captureset.
Coercion cset_fvar : atom >-> captureset.

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

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => if K === J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  (** No change here: capture sets are not affected by type substitution *)
  | typ_capt C T => typ_capt C (open_tt_rec K U T)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  (** Opening a type variable within an expression doesn't affect capture sets....
      no change here. *)
  end.

Fixpoint open_ct_rec (k : nat) (c : captureset) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar i => typ_bvar i
  | typ_fvar x => typ_fvar x
  (** A function type A -> B introduces a binding for a capture variable.
      Note that we don't allow capture variables to show up in their own type constraints. *)
  | typ_arrow T1 T2 => typ_arrow (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  | typ_all T1 T2 => typ_all (open_ct_rec k c T1) (open_ct_rec k c T2)
  (** We actually need to perform the substitution here. *)
  | typ_capt C T => typ_capt (open_cset k c C) (open_ct_rec k c T)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (c : captureset) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k === i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs t e1 => exp_abs (open_ct_rec k c t) (open_ee_rec (S k) f c e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f c e1) (open_ee_rec k f c e2)
  | exp_tabs t e1 => exp_tabs (open_ct_rec k c t) (open_ee_rec k f c e1)
  | exp_tapp e1 t => exp_tapp (open_ee_rec k f c e1) (open_ct_rec k c t)
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
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 c := open_ee_rec 0 e2 c e1.
Definition open_ct T c := open_ct_rec 0 c T.

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

Inductive capt : captureset -> Prop :=
  | capt_universal : capt cset_universal
  | capt_capturing : forall xs, capt (cset_set xs {}N)
  .

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_ct T2 (cset_fvar X))) ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
  | type_capt : forall C T,
      type T ->
      capt C ->
      type (typ_capt C T)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x x)) ->
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

Inductive polarity : Type :=
  | positive : polarity
  | negative : polarity
  | dontcare : polarity
  .

Inductive mode : Type :=
  | covariant : mode
  | contravariant : mode
  .

Definition polarity_from_mode (m : mode) : polarity :=
  match m with
  | covariant => positive
  | contravariant => negative
  end.

Definition neg (m : mode) : mode :=
  match m with
    | covariant => contravariant
    | contravariant => covariant
  end.

Definition cancapture (p : polarity) (m : mode) : Prop := 
  match p , m with
  | negative , covariant => False
  | negative , contravariant =>  True
  | positive , covariant => True
  | positive , contravariant => False
  | dontcare , _ => True
  end.


Inductive binding : Type :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> polarity -> binding.

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

(* TODO maybe define a polarized version of env as a tuple of env and context  *)
Notation env := (list (atom * binding)).
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
Definition allbound_typ (E : env) (m : mode) (X : atoms) : Prop :=
  forall x, AtomSet.F.In x X -> exists T p,
    cancapture p m /\ binds x (bind_typ T p) E.

Inductive wf_cset : env -> mode -> captureset -> Prop :=
  | wf_universal_cset : forall E m,
    wf_cset E m cset_universal
  | wf_concrete_cset : forall E m fvars,
    (allbound_typ E m fvars) ->
    wf_cset E m (cset_set fvars {}N)
.

(* Wellformedness of types where locally bound variables are only 
   allowed in positive positions. *)
Inductive wf_typ : env -> mode -> typ -> Prop :=
  | wf_typ_top : forall E m,
      wf_typ E m typ_top
  | wf_typ_var : forall U E m (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E m (typ_fvar X)
  | wf_typ_arrow : forall L E m T1 T2,
    wf_typ E (neg m) T1 ->
      (** NEW: we need to be able to open capture sets.  Capture
          variables can only be opened in covariant positions. *)
      (forall X : atom, X `notin` L ->
        wf_typ ([(X, bind_typ T1 (polarity_from_mode (neg m)))] ++ E) m (open_ct T2 X)) ->
       wf_typ E m (typ_arrow T1 T2)
  | wf_typ_all : forall L E m T1 T2,
      wf_typ E (neg m) T1 ->
      (forall X : atom, X `notin` L ->
      wf_typ ([(X, bind_sub T1)] ++ E) m (open_tt T2 X)) ->
      wf_typ E m (typ_all T1 T2)
  (** NEW: capture sets check if their variables are defined in covariant positions. *)
  | wf_typ_capt : forall E m C T,
    wf_typ E m T ->
    wf_cset E m C ->
    wf_typ E m (typ_capt C T)
.

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
  | wf_env_sub : forall (E : env) (m : mode) (X : atom) (T : typ),
      wf_env E ->
      (* TODO verify this when we check regularity *)
      wf_typ E m T ->
      X `notin` dom E ->
      wf_env ([(X, bind_sub T)] ++ E)
  | wf_env_typ : forall (E : env) (m : mode) (x : atom) (T : typ) (p : polarity),
      wf_env E ->
      (* TODO verify this when we check regularity *)
      wf_typ E m T ->
      x `notin` dom E ->
      wf_env ([(x, bind_typ T p)] ++ E).

(** Dealing with cv -- as a fixpoint is problematic. *)
Inductive cv : typ -> env -> captureset -> Prop :=
  (** C T has cv C cup cv T *)
  | cv_typ_capt : forall T E C1 C2,
    cv T E C2 ->
    cv (typ_capt C1 T) E (cset_union C1 C2)
  (** Looking up in the environment *)
  | cv_typ_var : forall (X : atom) T E C,
    binds X (bind_sub T) E ->
    cv T E C ->
    cv (typ_fvar X) E C
  (** Function types and arrow types are just {} *)
  | cv_typ_arrow : forall T1 T2 E,
    cv (typ_arrow T1 T2) E {}C
  | cv_typ_all : forall T1 T2 E,
    cv (typ_all T1 T2) E {}C
  (** Maybe: a capture-environment irrelevance term? *)
  | cv_top : forall E,
      cv typ_top E {}C
.


(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)


Inductive captures : env -> mode -> atoms -> atom -> Prop :=
  (* xs captures x if it includes it verbatim *)
  | captures_in : forall E m x xs,
      x `in` xs ->
      captures E m xs x
  (* xs captures x if it includes its capture set (cv) *)
  | captures_var : forall E m T p x xs ys,
      cancapture p m ->
      binds x (bind_typ T p) E ->
      cv T E (cset_set ys {}N) ->
      AtomSet.F.For_all (captures E m xs) ys ->
      captures E m xs x
.

Inductive subcapt : env -> mode -> captureset -> captureset -> Prop :=
  | subcapt_universal : forall E m C,
      wf_cset E m C ->
      subcapt E m C cset_universal
  | subcapt_set : forall E m xs ys,
      wf_cset E m (cset_set xs {}N) ->
      wf_cset E m (cset_set ys {}N) ->
      AtomSet.F.For_all (captures E m ys) xs ->
      subcapt E m (cset_set xs {}N) (cset_set ys {}N)
.


(** The definition of subtyping is straightforward.  It uses the
    [binds] relation from the [Environment] library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Inductive sub : env -> mode -> typ -> typ -> Prop :=
(* 
    cv(S, E) = {}
    -------------
     E ⊢ S <: ⊤
*)
  | sub_top : forall E m S,
      wf_env E ->
      wf_typ E m S ->
      (** NEW: S can't capture anything *)
      cv S E {}C ->
      sub E m S typ_top

  (* Instead of having rules for refl and trans, the original Fsub calculus special cases
     those rules to type variables. Refl and Trans are then defined externally in sub_reflexivity
     and sub_transitivity. *)
  | sub_refl_tvar : forall E m X,
      wf_env E ->
      wf_typ E m (typ_fvar X) ->
      sub E m (typ_fvar X) (typ_fvar X)

  | sub_trans_tvar : forall U E m T X,
      binds X (bind_sub U) E ->
      sub E m U T ->
      sub E m (typ_fvar X) T

(* 
    E ⊢ T₁ <: S₁    E, x: T₁ ⊢ S₂ <: T₂
    ------------------------------------
        E ⊢ ∀(x: S₁)S₂ <: ∀(x: T₁)T₂

    New: Here we open S2 and T2 with x
*)
  | sub_arrow : forall L E m S1 S2 T1 T2,
      sub E (neg m) T1 S1 ->
      (forall x : atom, x `notin` L ->
          sub ([(x, bind_typ T1 (polarity_from_mode (neg m)))] ++ E) m
            (open_ct S2 x) 
            (open_ct T2 x)) ->
      sub E m (typ_arrow S1 S2) (typ_arrow T1 T2)

(* 
    E ⊢ T₁ <: S₁    E, X<:T₁ ⊢ S₂ <: T₂
    ------------------------------------
       E ⊢ ∀[X<:S₁]S₂ <: ∀[X<:T₁]T₂
 *)
  | sub_all : forall L E c S1 S2 T1 T2,
      sub E (neg c) T1 S1 ->
      (forall X : atom, X `notin` L ->
          sub ([(X, bind_sub T1)] ++ E) c (open_tt S2 X) (open_tt T2 X)) ->
      sub E c (typ_all S1 S2) (typ_all T1 T2)
  
(*
    E ⊢ C₁ <: C₂    E ⊢ T₁ <: T₂
    -----------------------------
         E ⊢  C₁ T₁ <: C₂ T₂
*)
  | sub_capt : forall E c C1 C2 T1 T2,
      sub E c T1 T2 ->
      subcapt E c C1 C2 ->
      sub E c (typ_capt C1 T1) (typ_capt C2 T2)
.


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

(** A helper for computing the free variables of a term in an environment 
    Jonathan: Shouldn't we also compute the free variables in types?
*)
Inductive cv_free : exp -> captureset -> Prop :=
  | cv_free_bvar : forall n,
                    cv_free (exp_bvar n) {}C
  | cv_free_fvar : forall x,
                    cv_free (exp_fvar x) (cset_fvar x)
  | cv_free_abs : forall T e1 C,
                    cv_free e1 C ->
                    cv_free (exp_abs T e1) C
  | cv_free_app : forall e1 e2 C1 C2,
                    cv_free e1 C1 ->
                    cv_free e2 C2 ->
                    cv_free (exp_app e1 e2) (cset_union C1 C2)
  | cv_free_tabs : forall T e1 C,
                    cv_free e1 C ->
                    cv_free (exp_tabs T e1) C
  | cv_free_tapp : forall e1 T C,
                    cv_free e1 C ->
                    cv_free (exp_tapp e1 T) C
.

(** The definition of typing is straightforward.  It uses the [binds]
    relation from the [Environment] library (in the [typing_var] case)
    and cofinite quantification in the cases involving binders (e.g.,
    [typing_abs] and [typing_tabs]). *)

(*
 We assume the following invariant:
  env *only* contains dontcare bindings in the typing judgement 
 *)
Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T dontcare) E ->
      (** NEW: a variable always gets the type {x} T *)
      typing E (exp_fvar x) (typ_capt x T)
  | typing_abs : forall L E V e1 T1 C,
      (forall x : atom, x `notin` L ->
        wf_typ ([(x, bind_typ V positive)] ++ E) covariant (open_ct T1 x)  /\
        typing ([(x, bind_typ V dontcare)] ++ E) (open_ee e1 x x) T1) ->
      (** NEW: a function always gets the type C A -> B, where C = fv(body). 
          Formally we do U cv(x) | x free in body, but cv(x) = {x} by the above typing judgement. 

          In a type-variable-only-land, we'd probably do cv(x) = {T} if x : T in E.*)
      cv_free e1 C ->
      typing E (exp_abs V e1) (typ_capt C (typ_arrow V T1))
  | typing_app : forall T1 E e1 e2 T2 Cf Cv,
      typing E e1 (typ_capt Cf (typ_arrow T1 T2)) ->
      typing E e2 T1 ->
      cv T1 E Cv ->
      (** NEW: function application opens the capture set in the type. *)
      typing E (exp_app e1 e2) (open_ct T2 Cv)
  | typing_tabs : forall L E V e1 T1 C,
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_sub V)] ++ E) (open_te e1 X) (open_tt T1 X)) ->
      cv_free e1 C ->
      (* below is possibly unnecessary, should be deriveable from typing jdgmt precondition *)
      (* wf_typ E covariant (typ_all V T1) -> *)
      typing E (exp_tabs V e1) (typ_capt C (typ_all V T1))
  | typing_tapp : forall T1 E e1 T T2 C,
      typing E e1 (typ_capt C (typ_all T1 T2)) ->
      sub E covariant T T1 ->
      (* unsure about the below, probably should be wf_typ of T *)
      (* wf_typ E covariant (open_tt T2 T) -> *)
      typing E (exp_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E covariant S T ->
      typing E e T
.


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      expr (exp_tabs T e1) ->
      value (exp_tabs T e1)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      expr e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall T e1 v2 C,
      expr (exp_abs T e1) ->
      value v2 ->
      (** NEW: We open the capture set here with the computed capture set
          of the value, aka the free variables of the value.

          WIP: Maybe we shouldn't do this dynamic computation of capture sets,
          and explicitly write down which capture set we wish to substitute in. *)
      cv_free v2 C ->
      red (exp_app (exp_abs T e1) v2) (open_ee e1 v2 C)
  | red_tabs : forall T1 e1 T2,
      expr (exp_tabs T1 e1) ->
      type T2 ->
      red (exp_tapp (exp_tabs T1 e1) T2) (open_te e1 T2)
.


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

Hint Constructors type expr wf_typ wf_env value red cv sub captures subcapt typing wf_cset : core.
Hint Resolve sub_top sub_refl_tvar sub_arrow : core.
Hint Resolve typing_var typing_app typing_tapp typing_sub : core.
