Require Import Utils Ty.

(** definition of ordering between types **)

(* this inductive type encodes the ordering
   between two trust annotations as the least
   reflexive relation such that sec_ordering Trust Untrust *)

Inductive sec_ordering : secty -> secty -> Prop :=
  | so_trustuntrust : sec_ordering Trust Untrust
  | so_refl : forall t, sec_ordering t t.

(* the subtype relation *)

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

(* getting the trust annotation of a type *)

Definition sectyof (t : ty) : secty :=
  match t with
    | ty_bool s => s
    | arrow _ _ s => s
  end.

(* updating the trust annotation of a type *)

Definition update (t : ty) (s : secty) : ty :=
  match t with
    | (ty_bool _) => ty_bool s
    | (arrow l r _) => arrow l r s
  end.

(** least upper bound on trust annotations and their properties **)

Section LUB_SECTY.
  Definition lub_secty (x y : secty) : secty :=
    match x with
      | Trust    => y
      | Untrust  => Untrust
    end.

  Remark lub_unique : forall s s' s1, lub_secty s s' = s1 -> forall s2, lub_secty s s' = s2 -> s1 = s2.
  Proof.
    intros s s' s1 Hs1 s2 Hs2 ; destruct s ; destruct s' ; subst ; auto.
  Qed.
  
  Remark lub_secty_sym : forall s s', lub_secty s s' = lub_secty s' s.
  Proof.
    intros s s'; destruct s ; destruct s' ; auto.
  Qed.

  Remark subtype_bool_lub_secty : forall s s', subtype (ty_bool s) (ty_bool (lub_secty s s')).
  Proof.
    intros s s' ; destruct s ; destruct s' ; simpl ; auto.
  Qed.

  Remark sec_ordering_lub2 : forall s1 s2 s3, sec_ordering s1 s3 -> sec_ordering s2 s3 -> sec_ordering (lub_secty s1 s2) s3.
  Proof.
    intros s1 s2 s3 H1 H2 ; destruct s1 ; destruct s2 ; simpl ; auto.
  Qed.

  Remark sec_ordering_lub_refl : forall s, lub_secty s s = s.
  Proof.
    intros s ; destruct s ; simpl ; auto.
  Qed.
End LUB_SECTY.    

(* updating the trust annotation of a type with the least
   upper bound of its trust annotation and s. This is
   used in the type rule for applications *)

Definition update_secty (t : ty) (s : secty) : ty :=
  match t with
    | ty_bool s' => ty_bool (lub_secty s s')
    | arrow l r s' => arrow l r (lub_secty s s')
  end.

(* properties of trust annotations ordering *)

Remark sec_ordering_trans : forall s1 s2 s3, sec_ordering s1 s2 -> sec_ordering s2 s3 -> sec_ordering s1 s3.
Proof.
  intros s1 s2 s3 H1 H2 ; inv H1 ; inv H2 ; auto.
Qed.

Remark sec_ordering_bot : forall s, sec_ordering Trust s.
Proof.
  intros s ; destruct s ; auto.
Qed.

Remark sec_ordering_top1 : forall s, sec_ordering Untrust s -> s = Untrust.
Proof.
  intros s ; destruct s ; intro ; try solve by inversion ; auto.
Qed.

Remark subtype_refl : forall T, subtype T T.
Proof.
  intros T ; induction T ; auto.
Qed.

Hint Resolve sec_ordering_trans subtype_refl.

(* subtype relation is transitive *)

Remark subtype_trans : forall T1 T2 T3, subtype T1 T2 -> subtype T2 T3 -> subtype T1 T3.
Proof.
  intros T1 T2 T3.
  generalize dependent T1 ; generalize dependent T3.
  induction T2 ; intros ; inv H ; try solve by inversion ; try (inv H0) ; eauto.
Qed.

(* relating the ordering on trust annotations and the least upper bound function result *)

Remark sec_ordering_lub : forall s s', sec_ordering s (lub_secty s' s).
Proof with eauto.
  intros s s' ; destruct s ; destruct s' ...
Qed.

(* relating the subtype relation and the update of a trust annotation of a given type *)

Remark update_secty__subtype : forall T s, subtype T (update_secty T s).
Proof with eauto.
  intros T. induction T ; intros s1.
  destruct s ; destruct s1 ; simpl ...
  apply s_arrow ...
  apply sec_ordering_lub.
Qed.

(* more properties about updating/getting a trust annotations and the ordering relations *)

Remark update_secty_ident : forall T s, update_secty T s = update_secty (update_secty T s) s.
Proof.
  intros T s.
  induction T ; simpl.  
  destruct s ; destruct s0 ; simpl ; auto.
  destruct s ; destruct s0 ; simpl ; auto.
Qed.

Remark secty_update_eq :forall T T' s, subtype T T' -> sectyof T = sectyof (update_secty T s) -> sectyof T' = sectyof (update_secty T' s).
Proof.
  intros T T' s Hsub ; generalize dependent s ; induction Hsub ; intros ; simpl in *.
  destruct s' ; destruct s ; simpl in * ; destruct s0 ; try solve by inversion ; auto.
  destruct s1 ; destruct s ; simpl in * ; destruct s2 ; try solve by inversion ; auto.
Qed.

Remark update_secty_mono : forall T T' s s', subtype T T' -> sec_ordering s s' -> subtype (update_secty T s) (update_secty T' s').
Proof.
  intros T T' s s' Hsub Hsec ; induction Hsub ; inv Hsec ; 
    try repeat 
      (match goal with
           | [s : secty |- _] => destruct s
       end) ; simpl ; try solve by inversion ; auto.
Qed.

Remark subtype_trust_secty : forall T T', subtype T T' -> sectyof T' = Trust -> sectyof T = Trust.
Proof.
  intros T T' H ; induction H ; intros. inv H ; try solve by inversion ; auto.
  simpl in *. subst. inv H1. auto.
Qed.

Remark subtype_untrust_secty : forall T T', subtype T T' -> sectyof T = Untrust -> sectyof T' = Untrust.
Proof.
  intros T T' H ; induction H ; intros. inv H ; try solve by inversion ; auto.
  simpl in *. subst. inv H1. auto.
Qed.

Hint Resolve subtype_trans update_secty__subtype subtype_trust_secty 
             subtype_untrust_secty.
