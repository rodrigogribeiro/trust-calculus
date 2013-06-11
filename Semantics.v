(** definition of the small step semantics *)

Require Import Utils Syntax Ty.

(** definition of substitution **)

Fixpoint subst (x : id) (t : term) (t' : term) {struct t'} : term :=
  match t' with
    | tm_var i => if beq_id x i then t else t'
    | tm_app l r => tm_app (subst x t l) (subst x t r)
    | tm_abs i T t1 => tm_abs i T (if beq_id x i then t1 else (subst x t t1))
    | tm_trust t1 => tm_trust (subst x t t1)
    | tm_distrust t1 => tm_distrust (subst x t t1)
    | tm_check t1 => tm_check (subst x t t1)
    | tm_true        => tm_true
    | tm_false       => tm_false
  end.

(** definition of values *)

Inductive value : term -> Prop := 
  | v_true : value tm_true
  | v_false : value tm_false 
  | v_abs : forall x T t, value (tm_abs x T t).

Inductive untrust_value : term -> Prop :=
  | u_value : forall v, value v -> untrust_value (tm_distrust v).

Hint Constructors value untrust_value.

Reserved Notation "e '==>' e'" (at level 40).

(* the small step semantics relation *)

Inductive step : term -> term -> Prop :=
  | e_appabs : forall x T t12 v2, value v2 -> (tm_app (tm_abs x T t12) v2) ==> subst x v2 t12
  | e_app1   : forall t1 t1' t2, t1 ==> t1' -> tm_app t1 t2 ==> tm_app t1' t2
  | e_app2   : forall v1 t2 t2', value v1 -> t2 ==> t2' -> tm_app v1 t2 ==> tm_app v1 t2'
  | e_appabsu : forall v x T t12, untrust_value v -> tm_app (tm_abs x T t12) v ==> (subst x v t12)
  | e_app2u : forall v1 t2 t2', untrust_value v1 -> t2 ==> t2' -> tm_app v1 t2 ==> tm_app v1 t2' 
  (** other rules **)
  | e_trust1 : forall t1 t1', t1 ==> t1' -> tm_trust t1 ==> tm_trust t1'
  | e_distrust1 : forall t1 t1', t1 ==> t1' -> tm_distrust t1 ==> tm_distrust t1'
  | e_check1 : forall t1 t1', t1 ==> t1' -> tm_check t1 ==> tm_check t1'
  | e_distrustc1 : forall v, value v -> tm_trust (tm_distrust v) ==> tm_trust v
  | e_distrustd1 : forall v, value v -> tm_distrust (tm_distrust v) ==> tm_distrust v
  | e_distrusta1 : forall v x T t, value v -> tm_app (tm_distrust (tm_abs x T t)) v ==> tm_distrust (subst x v t)
  | e_distrusta2 : forall v x T t, untrust_value v -> tm_app (tm_distrust (tm_abs x T t)) v ==> tm_distrust (subst x v t)
  | e_trustv : forall t, value t -> tm_trust t ==> t
  | e_checkv : forall t, value t -> tm_check t ==> t
    where "t '==>' t'" := (step t t').

Hint Constructors step.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
   ~ (exists t', R t t').

Definition step_normal_form := normal_form step.

Hint Unfold normal_form step_normal_form.

Remark value_dont_step : forall t, value t -> ~ exists t', t ==> t'.
Proof.
  intros t H Hc. inv H ; try solve by inversion 2.
Qed.

Remark untrust_value_dont_step : forall t, untrust_value t -> ~ exists t', t ==> t'.
Proof.
  intros t Hu Hc. inv Hu.
  inv Hc. inv H0. apply value_dont_step in H. elim H ; eexists ; eauto.
  inv H.
Qed.

Ltac s := f_equal ; eauto ;
  try (match goal with
         | [H : value ?X, H1 : ?X ==> _ |- _] =>
           apply value_dont_step in H
         | [H : untrust_value ?X, H1 : ?X ==> _ |- _] =>
           apply untrust_value_dont_step in H
         | [H : False |- _] => elim H
         | [H : ~ _ |- _] => elim H
         | [H : tm_distrust _ ==> _ |- _] => inv H
         | [ |- ex _] => eexists ; eauto ; fail
       end) ; try solve by inversion ; unfold step_normal_form, normal_form in *.

(* this lemma proves that the previous semantics is deterministic *)

Lemma step_deterministic : forall t t', t ==> t' -> forall t'', t ==> t'' -> t' = t''.
Proof with eauto.
   intros t t' H ; induction H ; intros t'' H2 ; inv H2 ; repeat s ...
Qed.


(** multi step semantics **)

Definition multi_step := refl_step_closure step.

Notation "t '==>*' v" := (multi_step t v) (at level 40).





