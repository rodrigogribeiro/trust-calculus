Require Import SfLib Ty.

(** definition of ordering between types **)

Inductive sec_ordering : secty -> secty -> Prop :=
  | so_dontcare : forall t, sec_ordering t DontCare 
  | so_trustuntrust : sec_ordering Trust Untrust
  | so_refl : forall t, sec_ordering t t.

Inductive subtype : ty -> ty -> Prop :=
  | s_base : forall s s', sec_ordering s s' -> subtype (ty_bool s) (ty_bool s')
  | s_arrow : forall T1 T2 T1' T2' s1 s2,
              subtype T1' T1 ->
              subtype T2 T2' ->
              sec_ordering s1 s2 ->
              subtype (arrow T1 T2 s1) (arrow T1' T2' s2).

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first ; [Case_aux c "s_base" | Case_aux c "s_arrow"].

Hint Constructors sec_ordering subtype.

Definition sectyof (t : ty) : secty :=
  match t with
    | ty_bool s => s
    | arrow _ _ s => s
  end.

(** least upper bound on sec types **)

Definition lub_secty (x y : secty) : secty :=
  match x with
    | DontCare => DontCare
    | Trust    => y
    | Untrust  => match y with
                    | DontCare => DontCare
                    | _        => Untrust     
                  end
  end.

Definition update_secty (t : ty) (s : secty) : ty :=
  match t with
    | ty_bool s' => ty_bool (lub_secty s s')
    | arrow l r s' => arrow l r (lub_secty s s')
  end.

Remark sec_ordering_trans : forall s1 s2 s3, sec_ordering s1 s2 -> sec_ordering s2 s3 -> sec_ordering s1 s3.
Proof.
  intros s1 s2 s3 H1 H2 ; inv H1 ; inv H2 ; auto.
Qed.

Remark subtype_refl : forall T, subtype T T.
Proof.
  intros T ; induction T ; auto.
Qed.

Hint Resolve sec_ordering_trans subtype_refl.

Remark subtype_trans : forall T1 T2 T3, subtype T1 T2 -> subtype T2 T3 -> subtype T1 T3.
Proof.
  intros T1 T2 T3.
  generalize dependent T1 ; generalize dependent T3.
  induction T2 ; intros ; inv H ; try solve by inversion ; try (inv H0) ; eauto.
Qed.

Remark sec_ordering_lub : forall s s', sec_ordering s (lub_secty s' s).
Proof with eauto.
  intros s s' ; destruct s ; destruct s' ...
Qed.

Remark update_secty__subtype : forall T s, subtype T (update_secty T s).
Proof with eauto.
  intros T. induction T ; intros s1.
  destruct s ; destruct s1 ; simpl ...
  apply s_arrow ...
  apply sec_ordering_lub.
Qed.
 
Hint Resolve subtype_trans update_secty__subtype.

(** some simple examples **)

Definition BoolT := ty_bool Trust.
Definition BoolD := ty_bool DontCare.

Definition t1 := arrow BoolD BoolT Trust.
Definition t2 := arrow BoolT BoolT Trust.

Example test_subtype1 : subtype t1 t2.
Proof.
  unfold t1, t2, BoolT, BoolD.
  apply s_arrow.
  apply s_base.  
  auto.
  apply s_base.
  apply so_refl.
  apply so_refl.
Qed.

Example test_subtype2 : subtype BoolT BoolD.
Proof.
  apply s_base.
  apply so_dontcare.  
Qed.
