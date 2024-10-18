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
  | typ_cse : cse -> typ -> typ.

Coercion typ_var : var >-> typ.
Notation "'⊤'" := typ_top (at level 80, no associativity).
Notation "'∀' '(' S ')' T" := (typ_arr S T) (at level 60, S at next level, T at next level, right associativity).
Notation "'∀' '[' R ']' T" := (typ_all R T) (at level 60, R at next level, T at next level, right associativity).
Notation "'□' T" := (typ_box T) (at level 70, no associativity).
Notation "C '#' R" := (typ_cse C R) (at level 65, R at next level, right associativity).

Inductive exp : Type :=
  | exp_var : var -> exp
  | exp_loc : loc -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : var -> var -> exp
  | exp_let : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : var -> typ -> exp
  | exp_box : var -> exp
  | exp_unbox : cse -> var -> exp.

Coercion exp_var : var >-> exp.
Coercion exp_loc : loc >-> exp.
Notation "'λ' '(' T ')' Γ" := (exp_abs T Γ) (at level 60, T at next level, Γ at next level, right associativity).
Notation "'Λ' '[' R ']' Γ" := (exp_tabs R Γ) (at level 60, R at next level, Γ at next level, right associativity).
Notation "x '@' y" := (exp_app x y) (at level 61, y at next level, left associativity).
Notation "'let=' e1 'in' e2" := (exp_let e1 e2) (at level 59, e1 at next level, e2 at next level, right associativity).
Notation "x  '@' '[' R ']'" := (exp_tapp x R) (at level 61, R at next level, left associativity).
Notation "'box' Γ" := (exp_box Γ) (at level 70, Γ at next level, no associativity).
Notation "C '⟜' x" := (exp_unbox  C x) (at level 60, x at next level, right associativity).

Definition var_cv (v : var) : cse :=
  match v with
  | var_b _ => {}
  | var_f x => cse_fvar x
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
  | exp_loc l => l
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

Definition open_vv (k : nat) (z : atom) (v : var) : var :=
  match v with
  | var_b i => if k === i then z else i
  | var_f x => x
  end.

Fixpoint open_ve_rec (k : nat) (z : atom) (c : cse) (Γ : exp)  {struct Γ} : exp :=
  match Γ with
  | exp_var v => open_vv k z v
  | exp_loc l => l
  | λ (t) e1 => λ (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | f @ x => open_vv k z f @ open_vv k z x
  | let= Γ in C => let= open_ve_rec k z c Γ in open_ve_rec (S k) z c C
  | Λ [t] e1 => exp_tabs (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | x @ [t] => exp_tapp (open_vv k z x) (open_ct_rec k c t)
  | box x => box open_vv k z x
  | C ⟜ x => open_cse k (cse_fvar z) C ⟜ open_vv k z x
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te Γ U := open_te_rec 0 U Γ.
Definition open_ve Γ x c := open_ve_rec 0 x c Γ.
Definition open_ct T c := open_ct_rec 0 c T.

Fixpoint exp_cv (Γ : exp) : cse :=
  match Γ with
  | exp_var v => var_cv v
  | exp_loc l => cse_loc l
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
  | expr_loc : forall (l : loc),
      expr l
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x ∉ L -> expr (open_ve e1 x (cse_fvar x))) ->
      expr (λ (T) e1)
  | expr_app : forall (f x : atom),
      expr (f @ x)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x ∉ L -> expr (open_ve e2 x (cse_fvar x))) ->
      expr (let= e1 in e2)
  | expr_tabs : forall L R e1,
      pure_type R ->
      (forall X : atom, X ∉ L -> expr (open_te e1 X)) ->
      expr (Λ [R] e1)
  | expr_tapp : forall (x : atom) R,
      pure_type R ->
      expr (x @ [R])
  | expr_box : forall x : atom,
      expr (box x)
  | expr_unbox : forall C (x : atom),
      cset C ->
      expr (C ⟜ x).

Inductive binding : Type :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

Notation env := (list (atom * binding)).
Notation "∅" := (@nil (atom * binding)).

Notation "[ x ]" := (x :: nil).

Definition allbound (Γ : env) (fvars : atoms) : Prop :=
  forall x,
    x `in`A fvars ->
    exists C R, binds x (bind_typ (C # R)) Γ.

Reserved Notation "Γ '⊢ₛ' C 'wf'" (at level 40, C at next level, no associativity).

Inductive wf_cse : env -> cse -> Prop :=
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
      wf_cse E cse_bot
where "Γ '⊢ₛ' C 'wf'" := (wf_cse Γ C).

Reserved Notation "Γ '⊢' T 'wf'" (at level 40, T at next level, no associativity).

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_var : forall Γ X T,
      binds X (bind_sub T) Γ ->
      Γ ⊢ X wf
  | wf_typ_top : forall Γ,
      Γ ⊢ ⊤ wf
  | wf_typ_arr : forall L Γ C R T,
      Γ ⊢ (C # R) wf ->
      (forall x : atom, x ∉ L -> ([(x, bind_typ (C # R))] ++ Γ) ⊢ (open_ct T (cse_fvar x)) wf) ->
      Γ ⊢ ∀ (C # R) T wf
  | wf_typ_all : forall L Γ R T,
      Γ ⊢ R wf ->
      pure_type R ->
      (forall X : atom, X ∉ L -> ([(X, bind_sub R)] ++ Γ) ⊢ (open_tt T X) wf) ->
      Γ ⊢ ∀ [R] T wf
  | wf_typ_box : forall Γ T,
      Γ ⊢ T wf ->
      Γ ⊢ □ T wf
  | wf_typ_cse : forall Γ C R,
      Γ ⊢ₛ C wf ->
      Γ ⊢ R wf ->
      pure_type R ->
      Γ ⊢ C # R wf
where "Γ '⊢' T 'wf'" := (wf_typ Γ T).

Reserved Notation "Γ '⊢' 'wf'" (at level 40, no associativity).
Reserved Notation "Γ '⊢ₛ' C1 '<:' C2" (at level 40, C1 at next level, C2 at next level, no associativity). 
Reserved Notation "Γ '⊢' T1 '<:' T2" (at level 40, T1 at next level, T2 at next level, no associativity).
Reserved Notation "Γ '⊢' e ':' T" (at level 40, e at next level, T at next level, no associativity).
Reserved Notation "S '∷' Γ" (at level 40, Γ at next level, no associativity).
Reserved Notation "Γ '⊢' E ':' S '⇒' T" (at level 40, E at next level, S at next level, T at next level, no associativity).
Reserved Notation "Σ1 '-->' Σ2" (at level 40, Σ2 at next level, no associativity).

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      ∅ ⊢ wf
  | wf_env_sub : forall (Γ : env) (X : atom) (T : typ),
      Γ ⊢ wf ->
      Γ ⊢ T wf ->
      pure_type T ->
      X ∉ dom Γ ->
      ([(X, bind_sub T)] ++ Γ) ⊢ wf
  | wf_env_typ : forall (Γ : env) (x : atom) (C : cse) (R : typ),
      Γ ⊢ wf ->
      Γ ⊢ (C # R) wf ->
      x ∉ dom Γ ->
      ([(x, bind_typ (C # R))] ++ Γ) ⊢ wf
where "Γ '⊢' 'wf'" := (wf_env Γ).

Definition store_env : Set := list (loc * typ).

Inductive wf_store_ctx : store_env -> Prop :=
  | wf_store_nil :
      wf_store_ctx nil
  | wf_store_cons : forall l S C R,
      wf_store_ctx S ->
      wf_typ nil (C # R) ->
      l `Notin` (Store.dom S) ->
      wf_store_ctx ([(l, C # R)] ++ S).

Inductive subcapt : env -> store_env -> cse -> cse -> Prop :=
  | subcapt_top : forall E S Q,
      wf_env E ->
      wf_cse E Q ->
      subcapt E S cse_top Q
  | subcapt_bot : forall E S Q,
      wf_env E ->
      wf_cse E Q ->
      subcapt E S cse_bot Q
  | subcapt_refl_var : forall E S X,
      wf_env E ->
      wf_cse E (cse_fvar X) ->
      subcapt E S (cse_fvar X) (cse_fvar X)
  | subcapt_refl_loc : forall E S l,
      wf_env E ->
      wf_store_ctx S ->
      subcapt E S (cse_loc l) (cse_loc l)
  | subcapt_trans_var : forall R S E Q X T,
      binds X (bind_typ (typ_cse R T)) E ->
      subcapt E S R Q ->
      subcapt E S (cse_fvar X) Q
  | subcapt_trans_loc : forall E R S Q X T,
      Store.binds X (typ_cse R T) S ->
      subcapt E S R Q ->
      subcapt E S (cse_loc X) Q
  | subcapt_join_inl : forall E S R1 R2 Q,
      subcapt E S Q R1 ->
      wf_cse E R2 ->
      subcapt E S Q (cse_join R1 R2)
  | subcapt_join_inr : forall E S R1 R2 Q,
      wf_cse E R1 ->
      subcapt E S Q R2 ->
      subcapt E S Q (cse_join R1 R2)
  | subcapt_join_elim : forall E S R1 R2 Q,
      subcapt E S R1 Q ->
      subcapt E S R2 Q ->
      subcapt E S (cse_join R1 R2) Q.
(* where "Γ S '⊢ₛ' C1 <: C2" := (subcapt Γ S C1 C2). *)

Inductive sub : env -> store_env -> typ -> typ -> Prop :=
  | sub_refl_tvar : forall Γ (S: store_env) (X : atom),
      Γ ⊢ wf ->
      Γ ⊢ X wf ->
      sub Γ S X X
  | sub_trans_tvar : forall U S Γ T X,
      binds X (bind_sub U) Γ ->
      sub Γ S U T ->
      sub Γ S X T
  | sub_capt : forall Γ S C1 C2 R1 R2,
      subcapt Γ S C1 C2 ->
      sub Γ S R1 R2 ->
      pure_type R1 ->
      pure_type R2 ->
      sub Γ S (C1 # R1) (C2 # R2)
  | sub_top : forall Γ S T,
      Γ ⊢ wf ->
      Γ ⊢ T wf ->
      pure_type T ->
      sub Γ S T typ_top
  | sub_arr : forall L S Γ C1 R1 C2 R2 T1 T2,
      sub Γ S R2 R1 ->
      pure_type R1 ->
      pure_type R2 ->
      subcapt Γ S C2 C1 ->
      (forall x : atom, x ∉ L -> sub ([(x, bind_typ (C2 # R2))] ++ Γ) S (open_ct T1 (cse_fvar x)) (open_ct T2 (cse_fvar x))) ->
      sub Γ S (∀ (C1 # R1) T1) (∀ (C2 # R2) T2)
  | sub_all : forall L S Γ R1 R2 T1 T2,
      sub Γ S R2 R1 ->
      pure_type R1 ->
      pure_type R2 ->
      (forall X : atom, X ∉ L -> sub ([(X, bind_sub R2)] ++ Γ) S (open_tt T1 X) (open_tt T2 X)) ->
      sub Γ S (∀ [R1] T1) (∀ [R2] T2)
  | sub_box : forall Γ S T1 T2,
      sub Γ S T1 T2 ->
      sub Γ S (□ T1) (□ T2).
(* where "Γ S '⊢' T1 '<:' T2" := (sub Γ S T1 T2). *)

Inductive typing : env -> store_env -> exp -> typ -> Prop :=
  | typing_var : forall Γ x S C R,
      Γ ⊢ wf ->
      binds x (bind_typ (C # R)) Γ ->
      typing Γ S x (C # R)
  | typing_loc : forall Γ l S C R,
      wf_store_ctx S ->
      Store.binds l (C # R) S ->
      typing Γ S l (C # R)
  | typing_abs : forall L S Γ C R e1 T1,
      Γ ⊢ (C # R) wf ->
      (forall x : atom, x ∉ L ->
        typing ([(x, bind_typ (C # R))] ++ Γ) S (open_ve e1 x (cse_fvar x)) (open_ct T1 (cse_fvar x))) ->
      typing Γ S (λ (C # R) e1) (∀ (C # R) T1)
  | typing_app : forall S D Q Γ (f x : atom) T C,
      typing Γ S f (C # (∀ (D # Q) T)) ->
      typing Γ S x (D # Q) ->
      typing Γ S (f @ x) (open_ct T (cse_fvar x))
  | typing_let : forall S L C1 T1 T2 Γ e k,
      typing Γ S e (C1 # T1) ->
      (forall x : atom, x ∉ L ->
        typing ([(x, bind_typ (C1 # T1))] ++ Γ) S (open_ve k x (cse_fvar x)) T2) ->
      typing Γ S (let= e in k) T2
  | typing_tabs : forall S L Γ V e1 T1,
      Γ ⊢ V wf ->
      pure_type V ->
      (forall X : atom, X ∉ L ->
        typing ([(X, bind_sub V)] ++ Γ) S (open_te e1 X) (open_tt T1 X)) ->
      typing Γ S (Λ [V] e1) (exp_cv e1 # ∀ [V] T1)
  | typing_tapp : forall S Γ (x : atom) P Q T C,
      typing Γ S x (C # ∀ [P] T) ->
      sub Γ S P Q ->
      typing Γ S (x @ [P]) (open_tt T Q)
  | typing_box : forall Γ S (x : atom) C R,
      typing Γ S x (C # R) ->
      wf_cse Γ C ->
      typing Γ S (box x) ({} # □ (C # R))
  | typing_unbox : forall Γ S (x : atom) C R,
      typing Γ S x ({} # □ (C # R)) ->
      Γ ⊢ₛ C wf ->
      typing Γ S (C ⟜ x) (C # R)
  | typing_sub : forall S R Γ e T,
      typing Γ S e R ->
      sub Γ S R T ->
      typing Γ S e T.
(* where "Γ '⊢' e ':' T" := (typing Γ e T). *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (λ (T) e1) ->
      value (λ (T) e1)
  | value_tabs : forall T e1,
      expr (Λ [T] e1) ->
      value (Λ [T] e1)
  | value_box : forall e1,
      expr (box e1) ->
      value (box e1).

Inductive answer : exp -> Prop :=
  | answer_val : forall v,
      value v ->
      answer v
  | answer_var : forall (x : atom),
      answer x.

Inductive store_frame : Set :=
  | store (v : exp) : store_frame.

Definition store_ctx : Set := list (loc * store_frame).
Definition stores (S : store_ctx) (x : loc) (v : exp) : Prop :=
    Store.binds x (store v) S.

Inductive scope (k : exp) : Type :=
  | mk_scope : forall L, (forall x, x ∉ L -> expr (open_ve k x (cse_fvar x))) -> scope k.

Definition eval_ctx : Set := (list exp).

Inductive state : Set :=
  | mk_state : store_ctx -> store_env -> eval_ctx -> exp -> state.

Notation "⟨ S | L | E | Γ ⟩" := (mk_state S L E Γ) (at level 1).

Inductive state_final : state -> Prop :=
  | final_state : forall S a,
      answer a ->
      state_final ⟨ S | nil | a ⟩.

Inductive store_typing : store_ctx -> env -> Prop :=
  | typing_store_nil : nil ∷ nil
  | typing_store_cons : forall x C R v S Γ,
      S ∷ Γ ->
      value v ->
      Γ ⊢ v : (C # R) ->
      x ∉ dom Γ ->
      ([(x, store v)] ++ S) ∷ ([(x, bind_typ (C # R))] ++ Γ)
where "S '∷' Γ" := (store_typing S Γ).

Inductive eval_typing (Γ : env) : eval_ctx -> typ -> typ -> Prop :=
  | typing_eval_nil : forall C1 R1 C2 R2,
      Γ ⊢ (C1 # R1) <: (C2 # R2) ->
      Γ ⊢ nil : (C1 # R1) ⇒ (C2 # R2)
  | typing_eval_cons : forall L k E C1 R1 C2 R2 C3 R3,
      scope k ->
      (forall x, x ∉ L ->
        ([(x, bind_typ (C1 # R1))] ++ Γ) ⊢ open_ve k x (cse_fvar x) : (C2 # R2)) ->
      Γ ⊢ E : (C2 # R2) ⇒ (C3 # R3) ->
      Γ ⊢ (k :: E) : (C1 # R1) ⇒ (C3 # R3)
where "Γ '⊢' E ':' T '⇒' U" := (eval_typing Γ E T U).

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall S Γ E e C1 R1 C2 R2,
      S ∷ Γ ->
      Γ ⊢ E : (C1 # R1) ⇒ (C2 # R2) ->
      Γ ⊢ e : (C1 # R1) ->
      state_typing ⟨ S | E | e ⟩ (C2 # R2).

Inductive red : state -> state -> Prop :=
  | red_lift : forall x v k S K,
      value v ->
      x ∉ dom S ->
          ⟨ S | k :: K | v ⟩
      --> ⟨ [(x, store v)] ++ S | K | open_ve k x (cse_fvar x) ⟩
  | red_let_var : forall (x : atom) v k S K,
      stores S x v ->
          ⟨ S | k :: K | x ⟩
      --> ⟨ S | K | open_ve k x (cse_fvar x) ⟩
  | red_let_val : forall x v k S K,
      value v ->
      x ∉ dom S ->
          ⟨ S | K | let= v in k ⟩
      --> ⟨ [(x, store v )] ++ S | K | open_ve k x (cse_fvar x) ⟩
  | red_let_exp : forall e k (k_scope : scope k) S K,
          ⟨ S | K | let= e in k ⟩
      --> ⟨ S | k :: K | e ⟩
  | red_app : forall f x U e v S K,
      stores S f (λ (U) e) ->
      stores S x v ->
          ⟨ S | K | f @ x ⟩
      --> ⟨ S | K | open_ve e x (cse_fvar x) ⟩
  | red_tapp : forall x R U e S K,
      stores S x (Λ [U] e) ->
      pure_type R ->
          ⟨ S | K | x @ [R] ⟩
      --> ⟨ S | K | open_te e R ⟩
  | red_open : forall C x y S K,
      stores S x (box y) ->
          ⟨ S | K | C ⟜ x ⟩
      --> ⟨ S | K | y ⟩
where "Σ1 --> Σ2" := (red Σ1 Σ2).

Hint Constructors type pure_type expr cset wf_cse wf_typ wf_env value sub subcset typing : core.
Hint Resolve sub_top sub_refl_tvar sub_arr sub_all sub_box : core.
Hint Resolve typing_var typing_app typing_tapp typing_box typing_unbox typing_sub : core.

(* TODO: ???? *)
(* Local Ltac cset_unfold_union0 := *)
(*   match goal with *)
(*   | _ : _ |- context G [?C `u` (cset_set ?xs ?ns ?us)] => *)
(*     match C with *)
(*     | cset_set _ _ _ => *)
(*       rewrite cset_concrete_union *)
(*     | C => *)
(*       let HA := match goal with *)
(*                 | H : wf_cset _ C |- _ => H *)
(*                 | _ => *)
(*                   let H := fresh "WF" in *)
(*                   (* NOTE: avoid asserting (wf_cset _ _ C), it takes long to solve. *) *)
(*                   assert (wf_cset _ C) as HA by eauto; H *)
(*                 end *)
(*       in *)
(*       (* Invert, subst and clean up unnecessary hypothesis. *) *)
(*       pose proof ltac_mark; inversion HA; subst; clear_until_mark; *)
(*       (* Rewrite to avoid matching the same union twice, not sure if necessary. *) *)
(*       rewrite cset_concrete_union *)
(*     end *)
(*   end. *)
(**)
(* (* We can only define this tactic here, since in CaptureSets we don't have wf_cset. *) *)
(* Ltac cset_unfold_union := repeat cset_unfold_union0. *)
(**)
(* Ltac _csetsimpl_hook ::= cset_unfold_union. *)
