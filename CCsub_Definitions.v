Require Export TaktikZ.
Require Export Metatheory.
Require Export CaptureSets.
Require Import Coq.Program.Wf.

Notation "x '∈' L" := (x `in`A L) (at level 80, no associativity).
Notation "x '∉' L" := (x `notin`A L) (at level 80, no associativity).
Notation "xs '⊆' ys" := (xs `subset`A ys) (at level 80, no associativity).

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
  | exp_app : var-> var-> exp
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
      (forall X : atom, X `notin`A L -> type (open_ct T (cse_fvar X))) ->
      pure_type (∀ (S') T)
  | type_all : forall L R T,
      pure_type R ->
      (forall X : atom, X `notin`A L -> type (open_tt T X)) ->
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
      (forall x : atom, x `notin`A L -> expr (open_ve e1 x (cse_fvar x))) ->
      expr (λ (T) e1)
  | expr_app : forall (f x : var),
      expr (f @ x)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x `notin`A L -> expr (open_ve e2 x (cse_fvar x))) ->
      expr (let= e1 in e2)
  | expr_tabs : forall L R e1,
      pure_type R ->
      (forall X : atom, X `notin`A L -> expr (open_te e1 X)) ->
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
Notation store_ctx := (list (loc * typ)).
Notation "∅" := (@nil (atom * binding)).

Notation "[ x ]" := (x :: nil).

Definition allbound (Γ : ctx) (fvars : atoms) : Prop :=
  forall x,
    x `in`A fvars ->
    exists C R, binds x (bind_typ (C # R)) Γ.

Inductive wf_cse : ctx -> store_ctx -> cse -> Prop :=
  | wf_cse_top : forall Γ S,
      wf_cse Γ S cse_top
  | wf_cse_term_fvar : forall T S Γ (x : atom),
      binds x (bind_typ T) Γ ->
      wf_cse Γ S (cse_fvar x)
  | wf_cse_term_loc : forall S T Γ (l : loc),
      StoreImpl.binds l T S ->
      wf_cse Γ S (cse_loc l)
  | wf_cse_join : forall Γ S Q1 Q2,
      wf_cse Γ S Q1 ->
      wf_cse Γ S Q2 ->
      wf_cse Γ S (cse_join Q1 Q2)
  | wf_cse_bot : forall Γ S,
      wf_cse Γ S cse_bot.

Inductive wf_typ : ctx -> store_ctx -> typ -> Prop :=
  | wf_typ_var : forall Γ S X T,
      EnvImpl.binds X (bind_sub T) Γ ->
      wf_typ Γ S X
  | wf_typ_top : forall Γ S,
      wf_typ Γ S typ_top
  | wf_typ_arr : forall L Γ S C R T,
      wf_typ Γ S (C # R) ->
      (forall x : atom, x `notin`A L -> wf_typ ([(x, bind_typ (C # R))] ++ Γ) S (open_ct T (cse_fvar x))) ->
      wf_typ Γ S (∀ (C # R) T)
  | wf_typ_all : forall L S Γ R T,
      wf_typ Γ S R ->
      pure_type R ->
      (forall X : atom, X `notin`A L -> wf_typ ([(X, bind_sub R)] ++ Γ) S (open_tt T X)) ->
      wf_typ Γ S (∀ [R] T)
  | wf_typ_box : forall Γ S T,
      wf_typ Γ S T ->
      wf_typ Γ S (□ T)
  | wf_typ_capt : forall Γ S C R,
      wf_cse Γ S C ->
      wf_typ Γ S R ->
      pure_type R ->
      wf_typ Γ S (C # R).

Reserved Notation "S '∷' Γ" (at level 40, Γ at next level, no associativity).
Reserved Notation "Γ '⊢' E ':' S '⇒' T" (at level 40, E at next level, S at next level, T at next level, no associativity).
Reserved Notation "Σ1 '--->' Σ2" (at level 40, Σ2 at next level, no associativity).

Inductive wf_store_ctx : store_ctx -> Prop :=
  | wf_store_ctx_nil :
      wf_store_ctx nil
  | wf_store_ctx_cons : forall l S C R,
      wf_store_ctx S ->
      wf_typ nil S (C # R) ->
      l `notin`L (StoreImpl.dom S) ->
      wf_store_ctx ([(l, C # R)] ++ S).

Inductive wf_ctx : ctx -> store_ctx -> Prop :=
  | wf_ctx_empty : forall S,
      wf_store_ctx S ->
      wf_ctx nil S
  | wf_ctx_sub : forall (Γ : ctx) (S : store_ctx) (X : atom) (T : typ),
      wf_ctx Γ S ->
      wf_typ Γ S T ->
      pure_type T ->
      X ∉ EnvImpl.dom Γ ->
      wf_ctx ([(X, bind_sub T)] ++ Γ) S
  | wf_ctx_typ : forall (Γ : ctx) (S : store_ctx) (x : atom) (C : cse) (R : typ),
      wf_ctx Γ S ->
      wf_typ Γ S (C # R) ->
      x ∉ EnvImpl.dom Γ ->
      wf_ctx ([(x, bind_typ (C # R))] ++ Γ) S.

Inductive subcapt : ctx -> store_ctx -> cse -> cse -> Prop :=
  | subcapt_top : forall Γ S Q,
      wf_ctx Γ S ->
      wf_cse Γ S Q ->
      subcapt Γ S Q cse_top
  | subcapt_bot : forall Γ S Q,
      wf_ctx Γ S ->
      wf_cse Γ S Q ->
      subcapt Γ S cse_bot Q
  | subcapt_refl_var : forall Γ S X,
      wf_ctx Γ S ->
      wf_cse Γ S (cse_fvar X) ->
      subcapt Γ S (cse_fvar X) (cse_fvar X)
  | subcapt_refl_loc : forall Γ S l,
      wf_ctx Γ S ->
      wf_cse Γ S (cse_loc l) ->
      subcapt Γ S (cse_loc l) (cse_loc l)
  | subcapt_trans_var : forall R S Γ Q X T,
      binds X (bind_typ (typ_capt R T)) Γ ->
      subcapt Γ S R Q ->
      subcapt Γ S (cse_fvar X) Q
  | subcapt_trans_loc : forall Γ R S Q l T,
      StoreImpl.binds l (typ_capt R T) S ->
      subcapt Γ S R Q ->
      subcapt Γ S (cse_loc l) Q
  | subcapt_join_inl : forall Γ S R1 R2 Q,
      subcapt Γ S Q R1 ->
      wf_cse Γ S R2 ->
      subcapt Γ S Q (cse_join R1 R2)
  | subcapt_join_inr : forall Γ S R1 R2 Q,
      wf_cse Γ S R1 ->
      subcapt Γ S Q R2 ->
      subcapt Γ S Q (cse_join R1 R2)
  | subcapt_join_elim : forall Γ S R1 R2 Q,
      subcapt Γ S R1 Q ->
      subcapt Γ S R2 Q ->
      subcapt Γ S (cse_join R1 R2) Q.

Inductive sub : ctx -> store_ctx -> typ -> typ -> Prop :=
  | sub_refl_tvar : forall Γ (S: store_ctx) (X : atom),
      wf_ctx Γ S ->
      wf_typ Γ S X ->
      sub Γ S X X
  | sub_trans_tvar : forall U S Γ T X,
      EnvImpl.binds X (bind_sub U) Γ ->
      sub Γ S U T ->
      sub Γ S X T
  | sub_capt : forall Γ S C1 C2 R1 R2,
      subcapt Γ S C1 C2 ->
      sub Γ S R1 R2 ->
      pure_type R1 ->
      pure_type R2 ->
      sub Γ S (C1 # R1) (C2 # R2)
  | sub_top : forall Γ S T,
      wf_ctx Γ S ->
      wf_typ Γ S T ->
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

Inductive typing : ctx -> store_ctx -> exp -> typ -> Prop :=
  | typing_var : forall Γ x S C R,
      wf_ctx Γ S ->
      binds x (bind_typ (C # R)) Γ ->
      typing Γ S x (cse_fvar x # R)
  | typing_abs : forall L Γ C R e1 T1 S,
      wf_typ Γ S (C # R) ->
      (forall x : atom, x ∉ L ->
        typing ([(x, bind_typ (C # R))] ++ Γ) S (open_ve e1 x (cse_fvar x)) (open_ct T1 (cse_fvar x))) ->
      typing Γ S (λ (C # R) e1) (exp_cv e1 # ∀ (C # R) T1)
  | typing_app : forall D Q Γ (f x : atom) T C S,
      typing Γ S f (C # (∀ (D # Q) T)) ->
      typing Γ S x (D # Q) ->
      typing Γ S (f @ x) (open_ct T (exp_cv x))
  | typing_let : forall L C1 R1 T Γ e k S,
      typing Γ S e (C1 # R1) ->
      (forall x : atom, x ∉ L ->
        typing ([(x, bind_typ (C1 # R1))] ++ Γ) S (open_ve k x (cse_fvar x)) T) ->
      typing Γ S (let= e in k) T
  | typing_tabs : forall L Γ V e1 T1 S,
      wf_typ Γ S V ->
      pure_type V ->
      (forall X : atom, X ∉ L ->
        typing ([(X, bind_sub V)] ++ Γ) S (open_te e1 X) (open_tt T1 X)) ->
      typing Γ S (Λ [V] e1) (exp_cv e1 # ∀ [V] T1)
  | typing_tapp : forall Γ (x : atom) P Q T C S,
      typing Γ S x (C # ∀ [Q] T) ->
      sub Γ S P Q ->
      typing Γ S (x @ [P]) (open_tt T P)
  | typing_box : forall Γ S (x : atom) C R,
      typing Γ S x (C # R) ->
      wf_cse Γ S C ->
      typing Γ S (box x) ({} # □ (C # R))
  | typing_unbox : forall Γ S (x : atom) C R,
      typing Γ S x ({} # □ (C # R)) ->
      wf_cse Γ S C ->
      typing Γ S (C ⟜ x) (C # R)
  | typing_sub : forall R Γ e T S,
      typing Γ S e R ->
      sub Γ S R T ->
      typing Γ S e T.

Hint Constructors ok uniq StoreImpl.ok StoreImpl.uniq : core.
Hint Constructors type pure_type expr cset wf_cse wf_typ wf_ctx wf_store_ctx sub subcapt typing : core.
Hint Resolve sub_top sub_refl_tvar sub_arr sub_all sub_box : core.
Hint Resolve typing_var typing_app typing_tapp typing_box typing_unbox typing_sub : core.

