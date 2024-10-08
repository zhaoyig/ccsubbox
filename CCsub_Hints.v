Require Import Coq.Program.Equality.
Require Export CCsub_Lemmas.

Ltac destruct_union_mem H :=
  match type of H with
  | _ `in`A _ => rewrite AtomSetFacts.union_iff in H; destruct H as [H|H]
  end.

Hint Extern 1 (wf_typ ?Γ ?T) =>
match goal with
| H : wf_typ ?Γ (typ_cse _ ?P) |- _ =>
  inversion H; subst; (match goal with
                       | H : wf_typ ?Γ (typ_arr ?T _) |- _ =>
                         inversion H; subst; assumption
                       end)
end : core.

Hint Extern 1 (wf_cse ?Γ ?C) =>
match goal with
| H : typing ?Γ _ (typ_cse ?C _) |- _ =>
  let P := fresh "P" in
  pose proof (proj2 (proj2 (typing_regular _ _ _ H))) as P; inversion P; assumption
end : core.


Hint Extern 1 (wf_env ?Γ) =>
match goal with
| H : sub ?Γ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
end : core.


Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: subcset _ _ _ |- _ => apply (proj1 (subcapt_regular _ _ _ H))
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end : core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: type E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  end : core.


Hint Extern 1 (wf_cse ?E ?T) =>
  match goal with
  | H: subcset E T _ |- _ => apply (proj1 (proj2 (subcapt_regular _ _ _ H)))
  | H: subcset E _ T |- _ => apply (proj2 (proj2 (subcapt_regular _ _ _ H)))
  end : core.

Hint Extern 1 (cset ?T) =>
  let go E := apply (cset_from_wf_cset E); auto in
  match goal with
  | H: typing ?E _ (T # _) |- _ => go E
  | H: subcset ?E T _ |- _ => go E
  | H: subcset ?E _ T |- _ => go E
  end : core.

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
  end.

Ltac rewrite_parenthesise_binding_in H :=
  match type of H with
  | context[[(?x, ?b)] ++ ?F ++ ?E] =>
    rewrite_env (([(x, b)] ++ F) ++ E) in H
  end.

