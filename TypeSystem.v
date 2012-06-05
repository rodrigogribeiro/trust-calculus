
Require Import SfLib Syntax Ty Subtype Semantics.

(** Definition of the type system **)

Inductive has_type : context -> term -> ty -> Prop :=
  | T_True : forall ctx, has_type ctx tm_true (ty_bool Trust)
  | T_False : forall ctx, has_type ctx tm_false (ty_bool Trust)
  | T_Var : forall ctx v ty, 
        ctx v = Some ty -> has_type ctx (tm_var v) ty
  | T_Abs : forall ctx x t2 T1 T2, 
        has_type (extend ctx x T1) t2 T2 ->
        has_type ctx (tm_abs x T1 t2) (arrow T1 T2 Trust)
  | T_App : forall ctx t1 t2 T11 T12 s, 
        has_type ctx t1 (arrow T11 T12 s) -> 
        has_type ctx t2 T12 ->
        has_type ctx (tm_app t1 t2) (update_secty T12 s)
  | T_If : forall ctx t1 t2 t3 T,
        has_type ctx t1 BoolT ->
        has_type ctx t2 T     ->
        has_type ctx t3 T     -> 
        has_type ctx (tm_if t1 t2 t3) T
  | T_Trust : forall ctx t T,
        has_type ctx t T ->
        has_type ctx (tm_trust t) (update_secty T Trust)
  | T_Untrust : forall ctx t T,
        has_type ctx t T ->
        has_type ctx (tm_distrust t) (update_secty T Untrust)
  | T_Check : forall ctx t T,
        has_type ctx t T ->
        sectyof T = Trust ->
        has_type ctx (tm_check t) T
  | T_Sub : forall ctx t T T',
        has_type ctx t T ->
        subtype T T'     -> 
        has_type ctx t T'. 
                                     
Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first ; [Case_aux c "T_True"  | Case_aux c "T_False"   | Case_aux c "T_Var"   |
           Case_aux c "T_Abs"   | Case_aux c "T_App"     | Case_aux c "T_If"    |
           Case_aux c "T_Trust" | Case_aux c "T_Untrust" | Case_aux c "T_Check" |
           Case_aux c "T_Sub"].

(** inversion lemmas for subtyping **)

Lemma sub_inversion_base : 
  forall T s, subtype T (ty_bool s) -> exists s', sec_ordering s' s /\ T = (ty_bool s').
Proof with eauto.
  intros T s Hsub.
  remember (ty_bool s) as V.
  subtype_cases (induction Hsub) Case ; try (inv HeqV) ; try (eexists ; eauto ; fail).
Qed. 

Lemma sub_inversion_arrow : 
  forall T T1 T2 s, subtype T (arrow T1 T2 s) ->
    exists s', exists T1', exists T2',
      T = (arrow T1' T2' s') /\ subtype T1 T1' /\ subtype T2' T2 /\ sec_ordering s' s.
Proof.
  intros T T1 T2 s Hsub.
  remember (arrow T1 T2 s) as V.
  generalize dependent T2 ; revert T1 ; revert s.
  induction Hsub ; try solve by inversion ; try intros ; try (inv HeqV).
  repeat eexists ; repeat split ; eauto.
Qed.

(** canonical forms lemmas **)

Lemma canonical_forms_arrows : forall ctx t T1 T2 s,
  has_type ctx t (arrow T1 T2 s) ->
  value t ->
  exists x, exists S1, exists s2,
    t = tm_abs x S1 s2.
Proof with eauto.
  intros ctx t T1 T2 s Hty Hv.
  remember (arrow T1 T2 s) as V.
  generalize dependent T2 ; revert T1 ; revert s.
  has_type_cases (induction Hty) Case ; intros ; try (inv Hv ; solve by inversion 2).
  Case "T_Abs".
    repeat eexists ...
  Case "T_Sub".
    subst.
    apply sub_inversion_arrow in H.
    destruct H as [s' [T1' [T2' [HT [HS1 [HS2 HSS]]]]]].
    subst.
    eapply IHHty ...
Qed.

Lemma canonical_forms_bool : 
  forall ctx t s, has_type ctx t (ty_bool s) -> 
    value t -> t = tm_true \/ t = tm_false.
Proof with eauto.
  intros ctx t s Hty Hv ; remember (ty_bool s) as V.
  generalize dependent s.
  has_type_cases (induction Hty) Case ; try intros ; try solve by inversion 2 ...
  subst.
  apply sub_inversion_base in H.
  destruct H as [s' [Heq Hs]].
  eapply IHHty ...
Qed.

(** progress *)

Theorem progress : 
  forall t T, has_type empty t T ->
    value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Hty.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Hty) Case ; 
  intros Heq ; subst ; try (solve by inversion) ...
  Case "T_App".
    right.
    destruct IHHty1 ; subst ...
    SCase "t1 is a value".
      destruct IHHty2 ; subst ...
      SSCase "t2 is a value".
        destruct (canonical_forms_arrows empty t1 T11 T12 s) 
          as [x [S1 [s2 Heq]]] ... subst.
        exists (subst x t2 s2) ...
      SSCase "t2 can step".
        destruct H0 as [t2' Ht'] ; exists (tm_app t1 t2') ...
    SCase "t1 can step".
      destruct H as [t1' Ht1'].
      exists (tm_app t1' t2) ...
  Case "T_If".
    destruct IHHty1 ...
    SCase "t1 is a value".
      assert (Hb : t1 = tm_true \/ t1 = tm_false) by
        (eapply canonical_forms_bool ; eauto).
      inv Hb ...
    SCase "t1 can step".
      destruct H as [t1' Ht1'].
      right ; exists (tm_if t1' t2 t3) ...
  Case "T_Trust".
    destruct IHHty ...
    destruct H as [t' Ht'].
    right. exists (tm_trust t') ...
  Case "T_Untrust".
    destruct IHHty ...
    destruct H as [t' Ht'].
    right. exists (tm_distrust t') ...
  Case "T_Check".
    destruct IHHty ...
    destruct H0 as [t' Ht'].
    right. exists (tm_check t') ...
Qed.

(** inversion lemmas for the typing relation *)

Lemma typing_inversion_abs : 
  forall ctx x S1 s2 T, has_type ctx (tm_abs x S1 s2) T ->
    exists S2, exists s, subtype (arrow S1 S2 s) T /\
      has_type (extend ctx x S1) s2 S2.
Proof with eauto.
  intros ctx x S1 s2 T H.
  remember (tm_abs x S1 s2) as t.
  has_type_cases (induction H) Case ; inv Heqt ; intros ; try solve by inversion.
  Case "T_Abs".
    exists T2 ; exists Trust ; split ...   
  Case "T_Sub".
    destruct IHhas_type as [S2 [s' [H1 H2]]] ...
Qed.