(** definition of the small step semantics *)

Require Import SfLib Syntax.

Reserved Notation "t '==>' t'" (at level 40).

Fixpoint subst (x : id) (t : term) (t' : term) : term :=
  match t' with
    | tm_var i => if eq_id_dec x i then t else t'
    | tm_app l r => tm_app (subst x t l) (subst x t r)
    | tm_abs x T t1 => tm_abs x T (subst x t t1)
    | tm_trust t1 => tm_trust (subst x t t1)
    | tm_distrust t1 => tm_distrust (subst x t t1)
    | tm_check t1 => tm_check (subst x t t1)
    | tm_if t1 t2 t3 => tm_if (subst x t t1) (subst x t t2) (subst x t t3)
    | _              => t'
  end.

Inductive bvalue : term -> Prop :=
  | v_true : bvalue tm_true | v_false : bvalue tm_false.

Inductive absvalue : term -> Prop :=
  | v_abs : forall x T t12, absvalue (tm_abs x T t12).

Definition value (t : term) : Prop := bvalue t \/ absvalue t.

Hint Constructors bvalue absvalue.
Hint Unfold value.

Inductive step : term -> term -> Prop :=
  | e_appabs : forall x T t12 v2, value v2 -> (tm_app (tm_abs x T t12) v2) ==> subst x v2 t12
  | e_app1   : forall t1 t1' t2, t1 ==> t1' -> tm_app t1 t2 ==> tm_app t1' t2
  | e_app2   : forall v1 t2 t2', value v1 -> t2 ==> t2' -> tm_app v1 t2 ==> tm_app v1 t2'
  | e_iftrue : forall t2 t3, tm_if tm_true t2 t3 ==> t2
  | e_iffalse : forall t2 t3, tm_if tm_false t2 t3 ==> t3
  | e_if : forall t1 t1' t2 t3, t1 ==> t1' -> tm_if t1 t2 t3 ==> tm_if t1' t2 t3
  (** other rules **)
  | e_trust1 : forall t1 t1', t1 ==> t1' -> tm_trust t1 ==> tm_trust t1'
  | e_distrust1 : forall t1 t1', t1 ==> t1' -> tm_distrust t1 ==> tm_distrust t1'
  | e_check1 : forall t1 t1', t1 ==> t1' -> tm_check t1 ==> tm_check t1'
  | e_trustv : forall t, value t -> tm_trust t ==> t
  | e_distrustv : forall t, value t -> tm_distrust t ==> t
  | e_checkv : forall t, value t -> tm_check t ==> t
    where "t '==>' t'" := (step t t').

Hint Constructors step.

Remark value_dont_step : forall t, value t -> ~ exists t', t ==> t'.
Proof.
  intros t H Hc ;
  inv H ; inv H0 ; destruct Hc ; solve by inversion.
Qed.

Ltac s := f_equal ; eauto ;
  match goal with
    | [H : value ?X, H1 : ?X ==> _ |- _] =>
        apply value_dont_step in H ; elim H ; eexists 
  end.

Lemma step_deterministic : forall t t', t ==> t' -> forall t'', t ==> t'' -> t' = t''.
Proof.
   induction 1 ; intros t'' H2 ; inv H2 ;
   try solve by inversion ; repeat s.
Qed.
