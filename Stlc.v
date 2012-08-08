(** Standard definitions of a simple typed lambda calculus
    with booleans **)

Require Import Utils Context.

(** syntax definition **)

Inductive stlc_ty : Type :=
  | stlc_bool : stlc_ty
  | stlc_arrow : stlc_ty -> stlc_ty -> stlc_ty.

Inductive stlc_term : Type :=
  | stlc_true : stlc_term
  | stlc_false : stlc_term
  | stlc_var : id -> stlc_term
  | stlc_app : stlc_term -> stlc_term -> stlc_term
  | stlc_abs : id -> stlc_ty -> stlc_term -> stlc_term.

(** Semantics **)

Fixpoint subst (x : id) (t : stlc_term) (t' : stlc_term) {struct t'} : stlc_term :=
  match t' with
    | stlc_var i      => if beq_id x i then t else t'
    | stlc_app l r    => stlc_app (subst x t l) (subst x t r)
    | stlc_abs i T t1 => stlc_abs i T (if beq_id x i then t1 else (subst x t t1))
    | stlc_true       => stlc_true
    | stlc_false      => stlc_false
  end.

Inductive stlc_bvalue : stlc_term -> Prop :=
  | sv_true : stlc_bvalue stlc_true 
  | sv_false : stlc_bvalue stlc_false.

Inductive stlc_absvalue : stlc_term -> Prop :=
  | sv_abs : forall x T t12, stlc_absvalue (stlc_abs x T t12).

Definition stlc_value (t : stlc_term) : Prop := stlc_bvalue t \/ stlc_absvalue t.

Hint Constructors stlc_bvalue stlc_absvalue.
Hint Unfold stlc_value.

Reserved Notation "t '==>s' t'" (at level 40). 

Inductive stlc_step : stlc_term -> stlc_term -> Prop :=
  | se_appabs : forall x T t12 v2, stlc_value v2 -> (stlc_app (stlc_abs x T t12) v2) ==>s subst x v2 t12
  | se_app1   : forall t1 t1' t2, t1 ==>s t1' -> stlc_app t1 t2 ==>s stlc_app t1' t2
  | se_app2   : forall v1 t2 t2', stlc_value v1 -> t2 ==>s t2' -> stlc_app v1 t2 ==>s stlc_app v1 t2'
  where "t '==>s' t'" := (stlc_step t t').

Hint Constructors stlc_step.

Definition stlc_multi_step := refl_step_closure stlc_step.

Notation "t '==>s*' t'" := (stlc_multi_step t t') (at level 40).

(** typing **)

Definition stlc_context := finite_map stlc_ty.

Inductive stlc_has_type : stlc_context -> stlc_term -> stlc_ty -> Prop :=
  | ST_Var : forall Gamma x T,
      lookup x Gamma = Some T ->
      stlc_has_type Gamma (stlc_var x) T
  | ST_Abs : forall Gamma x T11 T12 t12,
      stlc_has_type (extend x T11 Gamma) t12 T12 -> 
      stlc_has_type Gamma (stlc_abs x T11 t12) (stlc_arrow T11 T12)
  | ST_App : forall T11 T12 Gamma t1 t2,
      stlc_has_type Gamma t1 (stlc_arrow T11 T12) -> 
      stlc_has_type Gamma t2 T11 -> 
      stlc_has_type Gamma (stlc_app t1 t2) T12
  | ST_True : forall Gamma,
       stlc_has_type Gamma stlc_true stlc_bool
  | ST_False : forall Gamma,
       stlc_has_type Gamma stlc_false stlc_bool.

Hint Constructors stlc_has_type.
