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

Definition env := list (atom * loc).
Definition exp_env: Set := (exp * env).

Inductive value : exp_env -> Prop :=
  | value_abs : forall T E e1,
      expr (λ (T) e1) ->
      (* fv_ve e1 = dom E -> *)
      value ((λ (T) e1), E)
  | value_tabs : forall T E e1,
      expr (Λ [T] e1) ->
      (* fv_ve e1 = dom E -> *)
      value ((Λ [T] e1), E)
  | value_box : forall E e1,
      expr (box e1) ->
      (* fv_ve e1 = dom E -> *)
      value ((box e1), E).

Inductive answer : exp_env -> Prop :=
  | answer_val : forall v E,
      value (v, E) ->
      answer (v, E).

Inductive store_frame : Set :=
  | store (v : exp_env) : store_frame.
Notation store_env := (list (loc * store_frame)).

Inductive frame : Set :=
  | let_body: exp_env -> frame.
Notation cont := (list frame).

Definition stores (x : loc) (v : exp_env) (SS : store_env) : Prop :=
    StoreImpl.binds x (store v) SS.

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
      x `notin`A dom Γ ->
      StoreImpl.binds l (C # R) S ->
      env_well_typed S ([(x, l)] ++ E) ([(x, bind_typ (cse_loc l # R))] ++ Γ).

Inductive loc_transform_cse : env -> cse -> cse -> Prop :=
  | loc_transform_cse_nil : forall C,
      loc_transform_cse nil C C
  | loc_transform_cse_multi : forall x l E C D,
      loc_transform_cse E (subst_cse x (cse_loc l) C) D ->
      loc_transform_cse ((x, l) :: E) C D.

Inductive loc_transform : env -> typ -> typ -> Prop :=
  | loc_transform_nil : forall T,
      loc_transform nil T T
  | loc_transform_multi : forall x l E T U,
      loc_transform E (subst_ct x (cse_loc l) T) U ->
      loc_transform ((x, l) :: E) T U.

Inductive loc_transform_exp : env -> exp -> exp -> Prop :=
  | loc_transform_exp_nil : forall e,
      loc_transform_exp nil e e
  | loc_transform_exp_multi : forall x (l : loc) E e1 e2,
      loc_transform_exp E (subst_ve x l (cse_loc l) e1) e2 ->
      loc_transform_exp ((x, l) :: E) e1 e2.

Inductive loc_transform_ctx : env -> ctx -> ctx -> Prop :=
  | loc_transform_ctx_nil : forall Γ,
      loc_transform_ctx nil Γ Γ
  | loc_transform_ctx_multi : forall x l E Γ Δ,
      loc_transform_ctx E (map (subst_cb x (cse_loc l)) Γ) Δ ->
      loc_transform_ctx ((x, l) :: E) Γ Δ.

Inductive frame_typing : store_ctx -> exp_env -> typ -> Prop :=
  | typing_frame_transform : forall S e E U T Γ,
      env_well_typed S E Γ ->
      typing Γ S e U ->
      loc_transform E U T ->
      frame_typing S (e, E) T
  | typing_frame_sub : forall S e E U T,
      frame_typing S (e, E) U ->
      sub nil S U T ->
      frame_typing S (e, E) T.

Inductive store_typing : store_env -> store_ctx  -> Prop :=
  | typing_store_nil:
      store_typing nil nil
  | typing_store_cons : forall l C R v SS E S,
      store_typing SS S ->
      value (v, E) ->
      frame_typing S (v, E) (C # R) ->
      l `notin`L StoreImpl.dom S ->
      store_typing ((l, store (v , E)) :: SS) ((l, (C # R)) :: S).

Inductive eval_typing (S : store_ctx) : cont -> typ -> typ -> Prop :=
  | typing_eval_nil : forall C1 R1,
      (* sub Γ S (C1 # R1) (C2 # R2) -> *)
      wf_typ nil S (C1 # R1) ->
      eval_typing S nil (C1 # R1) (C1 # R1)
  | typing_eval_cons : forall Γ L e K C1 R1 C2 R2 C2' R2' C3 R3 E,
      (* scope e -> *)
      (forall x, x ∉ L ->
        typing ([(x, bind_typ (C1 # R1))] ++ Γ) S (open_ve e x (cse_fvar x)) (C2 # R2)) ->
      env_well_typed S E Γ ->
      wf_typ Γ S (C2 # R2) ->
      loc_transform E (C2 # R2) (C2' # R2') ->
      eval_typing S K (C2' # R2') (C3 # R3) ->
      eval_typing S ((let_body (e, E)) :: K) (C1 # R1) (C3 # R3).

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall S E SS K C1 R1 C2 R2 e,
      store_typing SS S ->
      eval_typing S K (C1 # R1) (C2 # R2) ->
      frame_typing S (e, E) (C1 # R1) ->
      (* sub Γ' S (C3 # R3) (C1 # R1) -> *)
      (* typing Γ S e (C1 # R1) -> *)
      (* env_well_typed S E Γ -> *)
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
  | red_app : forall (x y z: atom) T e1 lx ly v E SS K E',
      binds x lx E ->
      binds y ly E ->
      stores lx (λ (T) e1,  E') SS ->
      stores ly v SS ->
      z `notin`A dom E' ->
      red ⟨ (exp_app x y, E) | SS | K ⟩
          ⟨ (open_ve e1 z (cse_fvar z), (z,  ly) :: E') | SS | K ⟩
  | red_tapp : forall (x : atom) l T T0 e1 E E' SS K,
      binds x l E ->
      stores l (Λ [T0] e1, E') SS ->
      red ⟨ (x @ [T], E) | SS | K ⟩
          ⟨ (open_te e1 T, E') | SS | K ⟩
  | red_let : forall b e E SS K,
      red ⟨ (let= b in e, E) | SS | K ⟩
          ⟨ (b, E) | SS | (let_body (e, E)) :: K ⟩
  | red_let_val : forall (z: atom) E K e v SS l,
      z `notin`A dom E ->
      l `notin`L StoreImpl.dom SS ->
      value v ->
      red ⟨ v | SS | (let_body (e, E)) :: K ⟩
          ⟨ (open_ve e z (cse_fvar z), (z, l) :: E) | (l, store v) :: SS | K ⟩
  | red_open : forall (x : atom) l x y C0 E E' SS K,
      binds x l E ->
      stores l (box y, E') SS ->
      red ⟨ (C0 ⟜ x, E) | SS | K ⟩
          ⟨ (exp_var_like y, E) | SS | K ⟩.

Hint Constructors value store_typing eval_typing state_typing frame_typing loc_transform loc_transform_cse loc_transform_exp loc_transform_ctx : core.
