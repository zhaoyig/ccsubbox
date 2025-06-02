Require Import CCsub_Definitions.
Require Import Coq.Program.Equality.
Require Import CCsub_Typing.

(*
   Notational conventions:
   ctx: Γ (var -> type)
   store_ctx: S (loc -> type)
   env: E (var -> (type, loc))
   exp_env: eE (val)
   store_env: SS (loc -> val)
   frame: k (exp_env, typ with a hole)
   cont: K (list of frames)
 *)

Definition env := list (atom * (typ * loc)).
Definition exp_env: Set := (exp * env).

Inductive value : exp_env -> Prop :=
  | value_abs : forall T E e1,
      expr (λ (T) e1) ->
      fv_ve e1 = dom E ->
      value ((λ (T) e1), E)
  | value_tabs : forall T E e1,
      expr (Λ [T] e1) ->
      fv_ve e1 = dom E ->
      value ((Λ [T] e1), E)
  | value_box : forall E e1,
      expr (box e1) ->
      fv_ve e1 = dom E ->
      value ((box e1), E).

Inductive answer : exp_env -> Prop :=
  | answer_val : forall v E,
      value (v, E) ->
      answer (v, E).

Inductive store_frame : Set :=
  | store (v : exp_env) : store_frame.
Notation store_env := (list (loc * store_frame)).

Inductive frame : Set :=
  | let_body: exp_env -> typ -> frame.
Notation cont := (list frame).

Definition stores (x : loc) (v : exp_env) (SS : store_env) : Prop :=
    Store.binds x (store v) SS.

Inductive state : Set :=
  | mk_state : exp_env -> store_env -> cont -> state.
Notation "⟨ eE | SS | K ⟩" := (mk_state eE SS K) (at level 1).

Inductive state_final : state -> Prop :=
  | final_state : forall SS a,
      answer a ->
      state_final ⟨ a | SS | nil ⟩.

Inductive env_well_typed : store_ctx -> env -> ctx -> Prop :=
  | env_empty : forall S,
      wf_store_ctx S ->
      env_well_typed S nil nil
  | env_cons : forall Γ S E x l C R,
      env_well_typed S E Γ ->
      x `notin` dom Γ ->
      Store.binds l (C # R) S ->
      env_well_typed S ([(x,  (C # R, l))] ++ E) ([(x, bind_typ (C # R))] ++ Γ).

Inductive store_typing : store_env -> store_ctx  -> Prop :=
  | typing_store_nil:
      store_typing nil nil
  | typing_store_cons : forall l C R v Γ SS E S,
      store_typing SS S ->
      value (v, E) ->
      env_well_typed S E Γ ->
      wf_typ nil S (C # R) ->
      typing Γ S v (C # R) ->
      l `Notin` Store.dom S ->
      store_typing ((l, store (v , E)) :: SS) ((l, (C # R)) :: S).

Inductive scope (e : exp) : Type :=
  | mk_scope : forall L, (forall x, x ∉ L -> expr (open_ve e x (cse_fvar x))) -> scope e.

Inductive eval_typing (Γ : ctx) (S : store_ctx) : cont -> typ -> typ -> Prop :=
  | typing_eval_nil : forall C1 R1 C2 R2,
      sub Γ S (C1 # R1) (C2 # R2) ->
      eval_typing Γ S nil (C1 # R1) (C2 # R2)
  | typing_eval_cons : forall L e K C1 R1 C2 R2 C3 R3 E,
      scope e ->
      (forall x, x ∉ L ->
        typing ([(x, bind_typ (C1 # R1))] ++ Γ) S (open_ve e x (cse_fvar x)) (C2 # R2)) ->
      env_well_typed S E Γ ->
      eval_typing Γ S K (C2 # R2) (C3 # R3) ->
      eval_typing Γ S ((let_body (e, E) (C1 # R1)) :: K) (C1 # R1) (C3 # R3).

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall Γ Γ' S E SS K C1 R1 C2 R2 e,
      store_typing SS S ->
      eval_typing Γ' S K (C1 # R1) (C2 # R2) ->
      typing Γ S e (C1 # R1) ->
      env_well_typed S E Γ ->
      state_typing ⟨ (e, E) | SS | K ⟩ (C2 # R2).

(* Inductive ee_typing : store_ctx -> exp_env -> typ -> Prop := *)
(*   | ee_typing_abs : forall Γ S E e1 T C R, *)
(*       env_well_typed S E Γ -> *)
(*       typing Γ S (λ (T) e1) (C # R) -> *)
(*       ee_typing S ((λ (T) e1), E) (C # R) *)
(*   | ee_typing_tabs : forall Γ S E e1 T C R, *)
(*       env_well_typed S E Γ -> *)
(*       typing Γ S (Λ [T] e1) (C # R) -> *)
(*       ee_typing S ((Λ [T] e1), E) (C # R) *)
(*   | ee_typing_box : forall Γ S E e1 C R, *)
(*       env_well_typed S E Γ -> *)
(*       typing Γ S (box e1) (C # R) -> *)
(*       ee_typing S ((box e1), E) (C # R). *)

Inductive red : state -> state -> Prop :=
  | red_app : forall (x y z: atom) T C1 R1 C2 R2 e1 lx ly v E SS K E',
      binds x (C1 # R1, lx) E ->
      binds y (C2 # R2, ly) E ->
      stores lx (λ (T) e1,  E') SS ->
      stores ly v SS ->
      (forall L, z `notin` L) ->
      red ⟨ (exp_app x y, E) | SS | K ⟩
          ⟨ (open_ve e1 z (cse_fvar z), (z,  (C2 # R2, ly)) :: E') | SS | K ⟩
  | red_tapp : forall (x : atom) T C R l T0 e1 E E' SS K,
      binds x (C # R, l) E ->
      stores l (Λ [T0] e1, E') SS ->
      red ⟨ (x @ [T], E) | SS | K ⟩
          ⟨ (open_te e1 T, E') | SS | K ⟩
  | red_let : forall b C R e E SS K,
      red ⟨ (let= b : (C # R) in e, E) | SS | K ⟩
          ⟨ (b, E) | SS | (let_body (e, E) (C # R)) :: K ⟩
  | red_let_val : forall (z: atom) C R E K e v SS l,
      z `notin` dom E ->
      l `Notin` Store.dom SS ->
      value v ->
      red ⟨ v | SS | (let_body (e, E) (C # R)) :: K ⟩
          ⟨ (open_ve e z (cse_fvar z), (z, (C # R, l)) :: E) | (l, store v) :: SS | K ⟩
  | red_open : forall (x : atom) C R l x y C0 E E' SS K,
      binds x (C # R, l) E ->
      stores l (box y, E') SS ->
      red ⟨ (C0 ⟜ x, E) | SS | K ⟩
          ⟨ ((exp_var y), E) | SS | K ⟩.

Hint Constructors value store_typing eval_typing state_typing : core.
