Require Import Context Stlc TypeSystem Syntax Ty Subtype List Utils Semantics.

(** Erasure **)

Fixpoint erase_ty (t : ty) : stlc_ty :=
  match t with
    | ty_bool _ => stlc_bool
    | arrow l r _ => stlc_arrow (erase_ty l) (erase_ty r)
  end.

Fixpoint erase_term (t : term) : stlc_term :=
  match t  with
    | tm_false => stlc_false
    | tm_true => stlc_true
    | tm_var i => stlc_var i
    | tm_app l r => stlc_app (erase_term l) (erase_term r)
    | tm_abs i T t => stlc_abs i (erase_ty T) (erase_term t)
    | tm_trust t => erase_term t
    | tm_distrust t => erase_term t
    | tm_check t => erase_term t
  end.

Definition erase_context (ctx : finite_map ty) : stlc_context :=
  map (fun p => match p with 
                  | (i,t) => (i, erase_ty t)
                end) ctx.

(** lemma 12 **)

Lemma subtype_erase : forall T T', subtype T T' -> erase_ty T = erase_ty T'.
Proof.
  intros T T' H ; induction H ; simpl ; f_equal ; auto.
Qed.

(** Theorem 13 **)

Lemma lookup_erase : forall i (t : ty) g, lookup i g = Some t -> lookup i (erase_context g) = Some (erase_ty t).
Proof.
  intros i t g H.
  induction g ; try solve by inversion.
  destruct a. simpl. remember (eq_id_dec i i0) as e ; destruct e ; subst ;auto.
  simpl in H. rewrite <- Heqe in H. inv H. auto.
  apply IHg. simpl in H. rewrite <- Heqe in H. auto.
Qed.

Lemma extend_erase : forall i (t : ty) g, erase_context (extend i t g) = extend i (erase_ty t) (erase_context g).
Proof.
  intros i t g ; induction g.
  simpl ; auto.
  destruct a ; simpl.
  remember (eq_id_dec i i0) as e ; destruct e ; subst ; auto.
  simpl. f_equal ; auto.
Qed.

Lemma update_secty_erase : forall t s, erase_ty (update_secty t s) = erase_ty t.
Proof.
  intros t s ; induction t ; simpl ; auto.
Qed.

Lemma subst_erase : forall x v t, erase_term (subst x v t) = Stlc.subst x (erase_term v) (erase_term t).
Proof.
  intros x v t ; induction t ; simpl ;  
    try (match goal with
           [ |- context[if beq_id ?X ?Y then _ else _]] => remember (beq_id X Y) as e ; destruct e
         end) ; auto.
   rewrite <- IHt1. rewrite <- IHt2. auto.
   rewrite <- IHt ; auto.
Qed.

Lemma value_erase : forall t, value t -> stlc_value (erase_term t).
Proof.
  intros t H ; inv H ; simpl ; auto.
Qed. 

Hint Resolve lookup_erase subtype_erase value_erase.

Theorem erase_typing : forall ctx e T, has_type ctx e T -> stlc_has_type (erase_context ctx) (erase_term e) (erase_ty T).
Proof with eauto.
  intros ctx e T HT.
  induction HT ; simpl ; try econstructor ...
  rewrite <- extend_erase ... 
  rewrite -> update_secty_erase ...
  rewrite -> update_secty_erase ...
  rewrite -> update_secty_erase ...
  apply subtype_erase in H.
  rewrite <- H ...
Qed.

(** simulation **)

Theorem simulation : forall ctx t T, has_type ctx t T -> exists v, (erase_term t) ==>s* v -> exists g, t ==>* g /\ (erase_term g) = v.
Proof.
  intros ctx t T HT.
  induction t ; try (eexists ; intros ; eexists ; split ; eauto ; try econstructor; fail).
Qed.  

