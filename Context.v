Require Import Utils Ty.

(** definition of finite maps as a list of pairs **)

Definition finite_map (A : Type) := list (id * A).

Definition empty {A : Type} : finite_map A := nil.

Fixpoint extend {A : Type} (x : id) (t : A) (gamma : finite_map A) :=
  match gamma with
    | nil => (x,t) :: nil
    | (y,t') :: gam => if eq_id_dec x y then (y,t) :: gam 
                         else (y,t') :: extend x t gam
      
  end.

Fixpoint lookup {A : Type} (x : id) (gamma : finite_map A) : option A :=
  match gamma with
    | nil => None
    | (y,t')::gam => if eq_id_dec x y then Some t'
                       else lookup x gam
  end.

(** Predicate for typing contexts **)

Inductive in_domain : id -> finite_map ty -> Prop :=
  | in_here : forall i t g, in_domain i ((i,t) :: g)
  | in_latter : forall i i' t' g, i <> i' -> in_domain i g -> in_domain i ((i',t')::g).

Hint Constructors in_domain.

Remark in_domain_nil : forall i, ~ in_domain i nil.
Proof.
  intros i ; intro H ; inv H.
Qed.

Remark in_dom_ex : forall i i' t g, in_domain i (extend i' t g) -> i = i' \/ in_domain i g.
Proof with auto.
  intros i i' t g Hd. 
  induction g. simpl in Hd.
  inv Hd. left ...
  solve by inversion. destruct a as [i0 t0].
  simpl in Hd. destruct (eq_id_dec i' i0) ; subst ...
  inv Hd. left ...
  right ; apply in_latter ...
  inv Hd. right ...
  apply IHg in H4.
  destruct H4 ; [left | right] ...
Qed.

Hint Resolve in_domain_nil in_dom_ex.

Inductive context : finite_map ty -> Prop :=
  | ctx_nil  : context nil
  | ctx_cons : forall i t g, context g -> ~ in_domain i g -> context ((i,t) :: g).

Hint Constructors context.

Lemma extend_preserves_context : forall i t g, context g -> context (extend i t g).
Proof.
  intros i t g Hc.  
  induction Hc ; simpl ; eauto.
  destruct (eq_id_dec i i0) ; subst ; auto.
  apply ctx_cons ; auto. intro Hc1.
  destruct (in_dom_ex i0 i t g Hc1) ;
     [subst ; elim n ; auto | idtac] ; contradiction.
Qed.

Lemma extend_lookup : forall {A : Type} x (t : A) g, lookup x (extend x t g) = Some t.
Proof.
  intros A x t g. induction g.
  simpl. remember (eq_id_dec x x) as e. destruct e ; auto.
  elim n ; auto.
  destruct a. simpl.
  remember (eq_id_dec x i) as e. destruct e ; auto.
  simpl. subst. remember (eq_id_dec i i) as e1. destruct e1 ; auto.
  elim n ; auto.
  simpl. remember (eq_id_dec x i) as e ; destruct e ; auto.
  inv Heqe.
Qed.

Lemma extend_lookup_neq : forall {A : Type} i i' (t : A) g, i <> i' -> lookup i (extend i' t g) = lookup i g.
Proof.
  intros A i i' t g He.
  induction g. simpl.
  remember (eq_id_dec i i') as e ; destruct e ; auto.
  unfold not in He. contradiction.
  destruct a. simpl.
  remember (eq_id_dec i' i0) as e1 ; destruct e1 ; subst ; auto ; try discriminate.
  simpl.
  remember (eq_id_dec i i0) as e' ; destruct e' ; subst ; auto ; try discriminate.
  elim He ; auto.
  simpl. remember (eq_id_dec i i0) as e2 ; destruct e2 ; subst ; auto.
Qed.

Lemma extend_override : forall {A : Type} i i' (t t' : A) g, lookup i (extend i' t (extend i' t' g)) = lookup i (extend i' t g).
Proof.
  intros A i i' t t' g.
  induction g ; simpl ; auto.
  remember (eq_id_dec i' i') as e ; destruct e ; subst ; auto ; try solve by inversion.
  remember (eq_id_dec i i') as e' ; destruct e' ; subst ; auto ; try solve by inversion.
  rewrite <- Heqe in Heqe'. inv Heqe'. elim n ; auto.
  destruct a. remember (eq_id_dec i' i0) as e ; destruct e ; subst ; auto ; try solve by inversion.
  simpl. rewrite <- Heqe. remember (eq_id_dec i i0) as e ; destruct e ; subst ; auto ; try solve by inversion.
  rewrite extend_lookup in IHg. simpl. rewrite <- Heqe. auto.
  simpl. rewrite <- Heqe0. auto.
  simpl. rewrite <- Heqe. remember (eq_id_dec i i0) as e0 ; destruct e0 ; subst ; auto ; try solve by inversion.
  simpl. rewrite <- Heqe0. auto.
  simpl. rewrite <- Heqe0. auto.
Qed.

Lemma extend_swap_neq : forall {A : Type} x i i' (t t' : A) g, i <> i' -> 
     lookup x (extend i t (extend i' t' g)) = lookup x (extend i' t' (extend i t g)).
Proof.
  intros A x i i' t t' g Heq.
  induction g. simpl.
  remember (eq_id_dec i i') as e ; destruct e ; subst ; auto.
  elim Heq ; auto. remember (eq_id_dec i' i)  as e' ; destruct e' ; subst ; auto.
  elim n ; auto. simpl.
  remember (eq_id_dec x i') as e1 ; destruct e1 ; subst ; auto.
  rewrite <- Heqe' ; auto.
  destruct a. simpl.
  remember (eq_id_dec i' i0) as e ; destruct e ; subst ; auto.
  remember (eq_id_dec i i0) as e' ; destruct e' ; subst ; auto.
  simpl. rewrite <- Heqe'. elim Heq ; auto. simpl. rewrite <- Heqe'.
  rewrite <- Heqe. auto.
  remember (eq_id_dec i i0) as e1 ; destruct e1 ; subst ; auto.
  simpl. rewrite <- Heqe1. rewrite <- Heqe. auto.
  simpl. rewrite <- Heqe1 ; rewrite <- Heqe. simpl.
  remember (eq_id_dec x i0) as e2 ; destruct e2 ; subst ; auto.
Qed.
