Require Export TaktikZ.
Require Export Metatheory.
Require Export CaptureSets.
Require Import Coq.Program.Wf.

Notation "x '∈' L" := (x `in` L) (at level 80, no associativity).
Notation "x '∉' L" := (x `notin` L) (at level 80, no associativity).
Notation "xs '⊆' ys" := (xs `subset` ys) (at level 80, no associativity).

Inductive typ : Type :=
  | typ_var : var -> typ
  | typ_top : typ
  | typ_arr : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_box : typ -> typ
  | typ_capt : cse -> typ -> typ.

Coercion typ_var : var >-> typ.
Notation "'⊤'" := typ_top (at level 80, no associativity).
Notation "'∀' '(' S ')' T" := (typ_arr S T) (at level 60, S at next level, T at next level, right associativity).
Notation "'∀' '[' R ']' T" := (typ_all R T) (at level 60, R at next level, T at next level, right associativity).
Notation "'□' T" := (typ_box T) (at level 70, no associativity).
Notation "C '#' R" := (typ_capt C R) (at level 65, R at next level, right associativity).

Inductive exp : Type :=
  | exp_var : var -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : var -> var -> exp
  | exp_let : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : var -> typ -> exp
  | exp_box : var -> exp
  | exp_unbox : cse -> var -> exp.

Coercion exp_var : var >-> exp.
Notation "'λ' '(' T ')' Γ" := (exp_abs T Γ) (at level 60, T at next level, Γ at next level, right associativity).
Notation "'Λ' '[' R ']' Γ" := (exp_tabs R Γ) (at level 60, R at next level, Γ at next level, right associativity).
Notation "x '@' y" := (exp_app x y) (at level 61, y at next level, left associativity).
Notation "'let=' e1 'in' e2" := (exp_let e1 e2) (at level 59, e1 at next level, e2 at next level, right associativity).
Notation "x  '@' '[' R ']'" := (exp_tapp x R) (at level 61, R at next level, left associativity).
Notation "'box' Γ" := (exp_box Γ) (at level 70, Γ at next level, no associativity).
Notation "C '⟜' x" := (exp_unbox  C x) (at level 60, x at next level, right associativity).

Definition var_cv (v: var) : cse :=
  match v with
  | var_f x => cse_fvar x
  | _ => {}
  end.

Definition open_vt (K : nat) (U : typ) (v : var) : typ :=
  match v with
  | var_b J => if K === J then U else J
  | var_f X => X
  end.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | C # R => C # open_tt_rec K U R
  | typ_var v => open_vt K U v
  | ⊤ => ⊤
  | ∀ (T1) T2 => ∀ (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | ∀ [T1] T2 => ∀ [open_tt_rec K U T1] (open_tt_rec (S K) U T2)
  | □ T => □ (open_tt_rec K U T)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (Γ : exp) {struct Γ} : exp :=
  match Γ with
  | exp_var v => exp_var v
  | λ (V) e1 => λ (open_tt_rec K U V) (open_te_rec (S K) U e1)
  | f @ x => exp_app f x
  | let= e1 in e2 => let= (open_te_rec K U e1) in (open_te_rec (S K) U e2)
  | Λ [V] e1 => Λ [open_tt_rec K U V] (open_te_rec (S K) U e1)
  | x @ [V] => x @ [open_tt_rec K U V]
  | box x => box x
  | C ⟜ x => C ⟜ x
  end.

Fixpoint open_ct_rec (k : nat) (c : cse) (T : typ)  {struct T} : typ :=
  match T with
  | typ_var v => v
  | C # R => open_cse k c C # open_ct_rec k c R
  | ⊤ => ⊤
  | ∀ (T1) T2 => ∀ (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  | ∀ [T1] T2 => ∀ [open_ct_rec k c T1] (open_ct_rec (S k) c T2)
  | □ T => □ (open_ct_rec k c T)
  end.

Definition open_vv (k : nat) (z : var) (v : var) : var :=
  match v with
  | var_b i => if k === i then z else i
  | var_f x => x
  end.

Fixpoint open_ve_rec (k : nat) (z : var) (c : cse) (Γ : exp)  {struct Γ} : exp :=
  match Γ with
  | exp_var v => open_vv k z v
  | λ (t) e1 => λ (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | f @ x => open_vv k z f @ open_vv k z x
  | let= Γ in C => let= open_ve_rec k z c Γ in open_ve_rec (S k) z c C
  | Λ [t] e1 => exp_tabs (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | x @ [t] => exp_tapp (open_vv k z x) (open_ct_rec k c t)
  | box x => box open_vv k z x
  | C ⟜ x => open_cse k (var_cv z) C ⟜ open_vv k z x
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te Γ U := open_te_rec 0 U Γ.
Definition open_ve Γ x c := open_ve_rec 0 x c Γ.
Definition open_ct T c := open_ct_rec 0 c T.

Fixpoint exp_cv (Γ : exp) : cse :=
  match Γ with
  | exp_var v => var_cv v
  | λ (t) e1 => exp_cv e1
  | f @ x => var_cv f `u` var_cv x
  | let= Γ in C => exp_cv Γ `u` exp_cv C
  | Λ [t] e1 => exp_cv e1
  | x @ [t] => var_cv x
  | box x => {}
  | C ⟜ x =>  `cse_remove_all_bvars` C `u` var_cv x
  end.

Inductive type : typ -> Prop :=
  | type_pure : forall R,
      pure_type R ->
      type R
  | type_cse : forall C R,
      cset C ->
      pure_type R ->
      type (C # R)
with pure_type : typ -> Prop :=
  | type_var : forall X : atom,
      pure_type X
  | type_top : pure_type typ_top
  | type_arr : forall L S' T,
      type S' ->
      (forall X : atom, X ∉ L -> type (open_ct T (cse_fvar X))) ->
      pure_type (∀ (S') T)
  | type_all : forall L R T,
      pure_type R ->
      (forall X : atom, X ∉ L -> type (open_tt T X)) ->
      pure_type (∀ [R] T)
  | type_box : forall T,
      type T ->
      pure_type (□ T).

Scheme type_mut := Induction for type Sort Prop
  with pure_mut := Induction for pure_type Sort Prop.
Combined Scheme type_mutind from type_mut, pure_mut.

Inductive expr : exp -> Prop :=
  | expr_var : forall (x : atom),
      expr x
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x ∉ L -> expr (open_ve e1 x (cse_fvar x))) ->
      expr (λ (T) e1)
  | expr_app : forall (f x : var),
      expr (f @ x)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x ∉ L -> expr (open_ve e2 x (cse_fvar x))) ->
      expr (let= e1 in e2)
  | expr_tabs : forall L R e1,
      pure_type R ->
      (forall X : atom, X ∉ L -> expr (open_te e1 X)) ->
      expr (Λ [R] e1)
  | expr_tapp : forall (x : var) R,
      pure_type R ->
      expr (x @ [R])
  | expr_box : forall x : var,
      expr (box x)
  | expr_unbox : forall C (x : var),
      cset C ->
      expr (C ⟜ x).

Inductive binding : Type :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

Notation ctx := (list (atom * binding)).
Notation store_ctx := (list (loc * (typ * ctx))).
Notation "∅" := (@nil (atom * binding)).

Notation "[ x ]" := (x :: nil).

Definition allbound (Γ : ctx) (fvars : atoms) : Prop :=
  forall x,
    x `in`A fvars ->
    exists C R, binds x (bind_typ (C # R)) Γ.

(* Change the order of ctx, store_ctx *)
Inductive wf_cse : ctx -> cse -> Prop :=
  | wf_cse_top : forall E,
      wf_cse E cse_top
  | wf_cse_term_fvar : forall T E (x : atom),
      binds x (bind_typ T) E ->
      wf_cse E (cse_fvar x)
  | wf_cse_join : forall E Q1 Q2,
      wf_cse E Q1 ->
      wf_cse E Q2 ->
      wf_cse E (cse_join Q1 Q2)
  | wf_cse_bot : forall E,
      wf_cse E cse_bot.

Inductive wf_typ : ctx -> typ -> Prop :=
  | wf_typ_var : forall Γ X T,
      binds X (bind_sub T) Γ ->
      wf_typ Γ X
  | wf_typ_top : forall Γ,
      wf_typ Γ typ_top
  | wf_typ_arr : forall L Γ C R T,
      wf_typ Γ (C # R) ->
      (forall x : atom, x ∉ L -> wf_typ ([(x, bind_typ (C # R))] ++ Γ) (open_ct T (cse_fvar x))) ->
      wf_typ Γ (∀ (C # R) T)
  | wf_typ_all : forall L Γ R T,
      wf_typ Γ R ->
      pure_type R ->
      (forall X : atom, X ∉ L -> wf_typ ([(X, bind_sub R)] ++ Γ) (open_tt T X)) ->
      wf_typ Γ (∀ [R] T)
  | wf_typ_box : forall Γ T,
      wf_typ Γ T ->
      wf_typ Γ (□ T)
  | wf_typ_capt : forall Γ C R,
      wf_cse Γ C ->
      wf_typ Γ R ->
      pure_type R ->
      wf_typ Γ (C # R).

Reserved Notation "S '∷' Γ" (at level 40, Γ at next level, no associativity).
Reserved Notation "Γ '⊢' E ':' S '⇒' T" (at level 40, E at next level, S at next level, T at next level, no associativity).
Reserved Notation "Σ1 '-->' Σ2" (at level 40, Σ2 at next level, no associativity).

Inductive wf_ctx : ctx ->  Prop :=
  | wf_ctx_empty :
      wf_ctx nil
  | wf_ctx_sub : forall (Γ : ctx) (X : atom) (T : typ),
      wf_ctx Γ ->
      wf_typ Γ T ->
      pure_type T ->
      X ∉ dom Γ ->
      wf_ctx ([(X, bind_sub T)] ++ Γ)
  | wf_ctx_typ : forall (Γ : ctx) (x : atom) (C : cse) (R : typ),
      wf_ctx Γ ->
      wf_typ Γ (C # R) ->
      x ∉ dom Γ ->
      wf_ctx ([(x, bind_typ (C # R))] ++ Γ).

Inductive wf_store_ctx : store_ctx -> Prop :=
  | wf_store_ctx_nil :
      wf_store_ctx nil
  | wf_store_ctx_cons : forall l Γ S C R,
      wf_store_ctx S ->
      wf_ctx Γ ->
      wf_typ Γ (C # R) ->
      l `Notin` (Store.dom S) ->
      wf_store_ctx ([(l, (C # R, Γ))] ++ S).

Inductive subcapt : ctx -> cse -> cse -> Prop :=
  | subcapt_top : forall Γ Q,
      wf_ctx Γ ->
      wf_cse Γ Q ->
      subcapt Γ Q cse_top
  | subcapt_bot : forall Γ Q,
      wf_ctx Γ ->
      wf_cse Γ Q ->
      subcapt Γ cse_bot Q
  | subcapt_refl_var : forall Γ X,
      wf_ctx Γ ->
      wf_cse Γ (cse_fvar X) ->
      subcapt Γ (cse_fvar X) (cse_fvar X)
  | subcapt_trans_var : forall R Γ Q X T,
      binds X (bind_typ (typ_capt R T)) Γ ->
      subcapt Γ R Q ->
      subcapt Γ (cse_fvar X) Q
  | subcapt_join_inl : forall Γ R1 R2 Q,
      subcapt Γ Q R1 ->
      wf_cse Γ R2 ->
      subcapt Γ Q (cse_join R1 R2)
  | subcapt_join_inr : forall Γ R1 R2 Q,
      wf_cse Γ R1 ->
      subcapt Γ Q R2 ->
      subcapt Γ Q (cse_join R1 R2)
  | subcapt_join_elim : forall Γ R1 R2 Q,
      subcapt Γ R1 Q ->
      subcapt Γ R2 Q ->
      subcapt Γ (cse_join R1 R2) Q.

Inductive sub : ctx -> typ -> typ -> Prop :=
  | sub_refl_tvar : forall Γ (X : atom),
      wf_ctx Γ ->
      wf_typ Γ X ->
      sub Γ X X
  | sub_trans_tvar : forall U Γ T X,
      binds X (bind_sub U) Γ ->
      sub Γ U T ->
      sub Γ X T
  | sub_capt : forall Γ C1 C2 R1 R2,
      subcapt Γ C1 C2 ->
      sub Γ R1 R2 ->
      pure_type R1 ->
      pure_type R2 ->
      sub Γ (C1 # R1) (C2 # R2)
  | sub_top : forall Γ T,
      wf_ctx Γ ->
      wf_typ Γ T ->
      pure_type T ->
      sub Γ T typ_top
  | sub_arr : forall L Γ C1 R1 C2 R2 T1 T2,
      sub Γ R2 R1 ->
      pure_type R1 ->
      pure_type R2 ->
      subcapt Γ C2 C1 ->
      (forall x : atom, x ∉ L -> sub ([(x, bind_typ (C2 # R2))] ++ Γ) (open_ct T1 (cse_fvar x)) (open_ct T2 (cse_fvar x))) ->
      sub Γ (∀ (C1 # R1) T1) (∀ (C2 # R2) T2)
  | sub_all : forall L Γ R1 R2 T1 T2,
      sub Γ R2 R1 ->
      pure_type R1 ->
      pure_type R2 ->
      (forall X : atom, X ∉ L -> sub ([(X, bind_sub R2)] ++ Γ) (open_tt T1 X) (open_tt T2 X)) ->
      sub Γ (∀ [R1] T1) (∀ [R2] T2)
  | sub_box : forall Γ T1 T2,
      sub Γ T1 T2 ->
      sub Γ (□ T1) (□ T2).

Inductive typing : ctx -> exp -> typ -> Prop :=
  | typing_var : forall Γ x C R,
      wf_ctx Γ ->
      binds x (bind_typ (C # R)) Γ ->
      typing Γ x (cse_fvar x # R)
  | typing_abs : forall L Γ C R e1 T1,
      wf_typ Γ (C # R) ->
      (forall x : atom, x ∉ L ->
        typing ([(x, bind_typ (C # R))] ++ Γ) (open_ve e1 x (cse_fvar x)) (open_ct T1 (cse_fvar x))) ->
      typing Γ (λ (C # R) e1) (exp_cv e1 # ∀ (C # R) T1)
  | typing_app : forall D Q Γ (f x : var) T C,
      typing Γ f (C # (∀ (D # Q) T)) ->
      typing Γ x (D # Q) ->
      typing Γ (f @ x) (open_ct T (exp_cv x))
  | typing_let : forall L C1 T1 T2 Γ e k,
      typing Γ e (C1 # T1) ->
      (forall x : atom, x ∉ L ->
        typing ([(x, bind_typ (C1 # T1))] ++ Γ) (open_ve k x (cse_fvar x)) T2) ->
      typing Γ (let= e in k) T2
  | typing_tabs : forall L Γ V e1 T1,
      wf_typ Γ V ->
      pure_type V ->
      (forall X : atom, X ∉ L ->
        typing ([(X, bind_sub V)] ++ Γ) (open_te e1 X) (open_tt T1 X)) ->
      typing Γ (Λ [V] e1) (exp_cv e1 # ∀ [V] T1)
  | typing_tapp : forall Γ (x : var) P Q T C,
      typing Γ x (C # ∀ [Q] T) ->
      sub Γ P Q ->
      typing Γ (x @ [P]) (open_tt T P)
  | typing_box : forall Γ (x : var) C R,
      typing Γ x (C # R) ->
      wf_cse Γ C ->
      typing Γ (box x) ({} # □ (C # R))
  | typing_unbox : forall Γ (x : var) C R,
      typing Γ x ({} # □ (C # R)) ->
      wf_cse Γ C ->
      typing Γ (C ⟜ x) (C # R)
  | typing_sub : forall R Γ e T,
      typing Γ e R ->
      sub Γ R T ->
      typing Γ e T.

Definition env := list (atom * loc).
Definition exp_env: Set := (exp * env).

Inductive value : exp_env -> Prop :=
  | value_abs : forall T E e1,
      expr (λ (T) e1) ->
      value ((λ (T) e1), E)
  | value_tabs : forall T E e1,
      expr (Λ [T] e1) ->
      value ((Λ [T] e1), E)
  | value_box : forall E e1,
      expr (box e1) ->
      value ((box e1), E).

Inductive answer : exp_env -> Prop :=
  | answer_val : forall v,
      value v ->
      answer v.

Inductive store_frame : Set :=
  | store (v : exp_env) : store_frame.

Notation store_env := (list (loc * store_frame)).

Definition stores (x : loc) (v : exp_env) (SS : store_env) : Prop :=
    Store.binds x (store v) SS.

Inductive frame : Set :=
  | let_body: exp_env -> frame.

Notation cont := (list frame).

Inductive state : Set :=
  | mk_state : exp_env -> store_env -> cont -> state.

Inductive scope (e : exp) : Type :=
  | mk_scope : forall L, (forall x, x ∉ L -> expr (open_ve e x (cse_fvar x))) -> scope e.

Notation "⟨ eE | SS | K ⟩" := (mk_state eE SS K) (at level 1).

(*
   Notational conventions:
   ctx: Γ
   store_ctx: S
   env: E
   exp_env: eE
   store_env: SS
   cont: K
   frame: k
 *)

Inductive state_final : state -> Prop :=
  | final_state : forall SS a,
      answer a ->
      state_final ⟨ a | SS | nil ⟩.

Inductive env_well_typed : ctx -> store_ctx -> env -> Prop :=
  | ee_empty : forall Γ S,
      wf_ctx Γ ->
      wf_store_ctx S ->
      env_well_typed Γ S nil
  | ee_cons : forall Γ Γ' S E x l T U,
      env_well_typed Γ S E ->
      binds x (bind_typ T) Γ ->
      Store.binds l (U, Γ') S ->
      sub Γ U T ->
      env_well_typed Γ S ((x, l)::E).

Inductive store_typing : store_env -> store_ctx  -> Prop :=
  | typing_store_nil:
      store_typing nil nil
  | typing_store_cons : forall l C R v Γ SS E S,
      store_typing SS S ->
      value (v, E) ->
      typing Γ v (C # R) ->
      env_well_typed Γ S E ->
      l `Notin` Store.dom S ->
      store_typing ((l, store (v , E)) :: SS) ((l, (C # R, Γ)) :: S).

Inductive eval_typing (Γ: ctx) (S: store_ctx) : cont -> typ -> typ -> Prop :=
  | typing_eval_nil : forall C1 R1 C2 R2,
      sub Γ (C1 # R1) (C2 # R2) ->
      eval_typing Γ S nil (C1 # R1) (C2 # R2)
  | typing_eval_cons : forall L e K C1 R1 C2 R2 C3 R3 E,
      scope e ->
      (forall x, x ∉ L ->
        typing ([(x, bind_typ (C1 # R1))] ++ Γ) (open_ve e x (cse_fvar x)) (C2 # R2)) ->
      env_well_typed Γ S E ->
      eval_typing Γ S K (C2 # R2) (C3 # R3) ->
      eval_typing Γ S ((let_body (e, E)) :: K) (C1 # R1) (C3 # R3).

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall Γ S E SS K C1 R1 C2 R2 e,
      store_typing SS S ->
      eval_typing Γ S K (C1 # R1) (C2 # R2) ->
      typing Γ e (C1 # R1) ->
      env_well_typed Γ S E ->
      state_typing (mk_state (e, E) SS K) (C2 # R2).

Inductive red : state -> state -> Prop :=
  | red_var : forall (x : atom) l SS K Γ eE,
      binds x l Γ ->
      stores l eE SS ->
      red ⟨ (exp_var x, Γ) | SS | K ⟩
          ⟨ eE | SS | K ⟩
  | red_app : forall (x y z: atom) T e1 lx ly v Γ SS K Γ',
      binds x lx Γ ->
      binds y ly Γ ->
      stores lx (λ (T) e1,  Γ') SS ->
      stores ly v SS ->
      z `notin` dom Γ' ->
      red ⟨ (exp_app x y, Γ) | SS | K ⟩
          ⟨ (open_ve e1 z (cse_fvar z), (z, ly) :: Γ') | SS | K ⟩
  | red_tapp : forall (x : atom) T l R e1 Γ Γ' SS K,
      binds x l Γ ->
      stores l (Λ [R] e1, Γ') SS ->
      red ⟨ (x @ [T], Γ) | SS | K ⟩
          ⟨ (open_te e1 T, Γ') | SS | K ⟩
  | red_let : forall b e Γ SS K,
      red ⟨ (let= b in e, Γ) | SS | K ⟩
          ⟨ (b, Γ) | SS | (let_body (e, Γ)) :: K ⟩
  | red_let_val : forall (z: atom) Γ K e v SS l,
      z `notin` dom Γ ->
      l `Notin` Store.dom SS ->
      value v ->
      red ⟨ v | SS | (let_body (e, Γ)) :: K ⟩
          ⟨ (open_ve e z (cse_fvar z), (z, l) :: Γ) | (l, store v) :: SS | K ⟩
  | red_open : forall (x : atom) l x y C Γ Γ' SS K,
      binds x l Γ ->
      stores l (box y, Γ') SS ->
      red ⟨ (C ⟜ x, Γ) | SS | K ⟩
          ⟨ ((exp_var y), Γ) | SS | K ⟩.

Hint Constructors type pure_type expr cset wf_cse wf_typ wf_ctx wf_store_ctx value sub subcapt typing : core.
Hint Resolve sub_top sub_refl_tvar sub_arr sub_all sub_box : core.
Hint Resolve typing_var typing_app typing_tapp typing_box typing_unbox typing_sub : core.

