Require Import Metatheory.
Require Import AssocList.

Tactic Notation
    "pick" "fresh" ident(atom_name)
    "excluding" constr(L)
    "and" "destruct" constr(H) :=
  let L := beautify_fset L in
  pick fresh atom_name for L;
  first [ destruct (@H atom_name ltac:(fsetdec))
        | edestruct (@H atom_name ltac:(fsetdec))].

Tactic Notation
    "pick" "fresh" ident(atom_name)
    "excluding" constr(L)
    "and" "destruct" constr(H) "as" simple_intropattern(pat) :=
  let L := beautify_fset L in
  pick fresh atom_name for L;
  first [ destruct (@H atom_name ltac:(fsetdec)) as pat
        | edestruct (@H atom_name ltac:(fsetdec)) as pat].

Tactic Notation
    "pick" "fresh" ident(atom_name)
    "excluding" constr(L)
    "and" "specialize" constr(H) :=
  let L := beautify_fset L in
  pick fresh atom_name for L;
  specialize (@H atom_name ltac:(fsetdec)).

Notation "E `subset`A F" :=
  (AtomSetImpl.Subset E F)
  (at level 68)
  : set_scope.

Ltac notin_simpl := AtomSetNotin.destruct_notin.
Ltac notin_solve := AtomSetNotin.solve_notin.
Ltac lnotin_simpl := LocSetNotin.destruct_notin.

Lemma atomset_subset_union : forall A1 A2 B1 B2,
  AtomSetImpl.Subset A1 A2 ->
  AtomSetImpl.Subset B1 B2 ->
  AtomSetImpl.Subset (AtomSetImpl.union A1 B1) (AtomSetImpl.union A2 B2).
Proof.
  intros.
  fsetdec.
Qed.

Lemma binds_remove_mid_cons :
  forall (A : Type) (x y : atom) (a b : A) (F G : list (atom * A)),
  binds x a (F ++ (y, b) :: G) -> x <> y -> binds x a (F ++ G).
Proof. intros *. clear. intros H. analyze_binds H. Qed.

Lemma fresh_mid : 
  forall (A : Type) (x : atom) (a : A) (E F : list (atom * A)),
  uniq (F ++ x ~ a ++ E) -> x `notin`A union (dom F) (dom E).
Proof. intros *. clear. solve_uniq. Qed.

Lemma nil_concat : forall (A: Type) (E: list (atom * A)),
  nil ++ E = E.
Proof.
  reflexivity.
Qed.

Ltac rewrite_nil_concat :=
  match goal with
  | |- _ ?E0 =>
    rewrite <- nil_concat with (E := E0)
  | |- _ ?E0 _ =>
    rewrite <- nil_concat with (E := E0)
  | |- _ ?E0 _ _ =>
    rewrite <- nil_concat with (E := E0)
  | |- _ ?E0 _ _ _ =>
    rewrite <- nil_concat with (E := E0)
  end.
