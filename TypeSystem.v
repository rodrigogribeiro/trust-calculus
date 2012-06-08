
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
  | T_App : forall ctx t1 t2 T11 T11' T12 s, 
        has_type ctx t1 (arrow T11 T12 s) -> 
        has_type ctx t2 T11' ->
        subtype T11' T11     ->
        has_type ctx (tm_app t1 t2) (update_secty T12 s)
  | T_If : forall ctx t1 t2 t3 T s,
        has_type ctx t1 (ty_bool s) ->
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

Hint Constructors has_type.

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

Hint Resolve sub_inversion_base sub_inversion_arrow.

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
         destruct H1 as [t2' Ht'] ; exists (tm_app t1 t2') ...
    SCase "t1 can step".
      destruct H0 as [t1' Ht1'].
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
    exists S2,  subtype (arrow S1 S2 Trust) T /\
      has_type (extend ctx x S1) s2 S2.
Proof with eauto.
  intros ctx x S1 s2 T H.
  remember (tm_abs x S1 s2) as t.
  has_type_cases (induction H) Case ; inv Heqt ; intros ; try solve by inversion.
  Case "T_Abs".
    exists T2 ; split ...   
  Case "T_Sub".
    destruct IHhas_type as [S2 [H1 H2]] ...
Qed.

Lemma typing_inversion_var : 
  forall ctx x T, has_type ctx (tm_var x) T ->
    exists S, ctx x = Some S /\ subtype S T.
Proof with eauto.
  intros ctx x T Hty.
  remember (tm_var x) as V.
  has_type_cases(induction Hty) Case ; intros ; inv HeqV ; try solve by inversion.
  Case "T_Var".
    repeat eexists ...
  Case "T_Sub".
    destruct IHHty ...
    exists x0.    
    destruct H0.
    split ...
Qed.

Lemma typing_inversion_true : 
  forall ctx T, has_type ctx tm_true T ->
    subtype (ty_bool Trust) T.
Proof with eauto.
  intros ctx T Hty.
  remember tm_true as t.
  has_type_cases (induction Hty) Case ; inv Heqt...
Qed.

Lemma typing_inversion_false :
  forall ctx T, has_type ctx tm_false T ->
    subtype (ty_bool Trust) T.
Proof with eauto.
  intros ctx T Hty.
  remember tm_false as t.
  has_type_cases (induction Hty) Case ; inv Heqt ...
Qed.

Lemma typing_inversion_app :
  forall ctx t1 t2 T2, has_type ctx (tm_app t1 t2) T2 ->
    exists T1, exists T11, exists s, 
      has_type ctx t1 (arrow T1 T2 s) /\ has_type ctx t2 T11 /\ subtype T11 T1 /\ sectyof T2 = sectyof (update_secty T2 s).
Proof with eauto.
  intros ctx t1 t2 T2 Hty.
  remember (tm_app t1 t2) as t.
  has_type_cases (induction Hty) Case ; intros ; inv Heqt ; try solve by inversion ...
  Case "T_App".
    repeat eexists...
    rewrite <- update_secty_ident ...
  Case "T_Sub".
    destruct IHHty ...
    destruct H0 as [T11 [s [H1 [H2 [H3 H4]]]]].
    repeat eexists ... eapply secty_update_eq ...
Qed.

Lemma typing_inversion_trust : 
  forall ctx t T, has_type ctx (tm_trust t) T ->
    exists T', has_type ctx t T' /\ subtype (update_secty T' Trust) T.
Proof with eauto.
   intros ctx t T Hty.
   remember (tm_trust t) as V.
   has_type_cases (induction Hty) Case ; inv HeqV ; try solve by inversion ...
   Case "T_Sub".
     destruct IHHty ...
     destruct H0 as [H1 H2].
     eexists ; split ...
Qed.

Lemma typing_inversion_distrust :
  forall ctx t T, has_type ctx (tm_distrust t) T ->
    exists T', has_type ctx t T' /\ subtype (update_secty T' Untrust) T.
Proof with eauto.
  intros ctx t T Hty.
  remember (tm_distrust t) as V.
  has_type_cases (induction Hty) Case ; inv HeqV ; try solve by inversion ...
  Case "T_Sub".
    destruct IHHty ...
    destruct H0 as [H1 H2].
    eexists ; split ...
Qed.

Lemma typing_inversion_check : 
  forall ctx t T, has_type ctx (tm_check t) T ->
    exists T', has_type ctx t T' /\ subtype T' T /\ sectyof T' = Trust.
Proof with eauto.
  intros ctx t T Hty.
  remember (tm_check t) as V.
  has_type_cases (induction Hty) Case ; inv HeqV ; try solve by inversion.
  Case "T_Check".
    eexists ; split ...
  Case "T_Sub".
    destruct IHHty as [T1 [H1 [H2 H3]]] ...
Qed.

Lemma typing_inversion_if :
  forall ctx t1 t2 t3 T, has_type ctx (tm_if t1 t2 t3) T ->
    exists s, has_type ctx t1 (ty_bool s) /\ has_type ctx t2 T /\ has_type ctx t3 T.
Proof with eauto.
  intros ctx t1 t2 t3 T Hty.
  remember (tm_if t1 t2 t3) as V.
  has_type_cases (induction Hty) Case ; inv HeqV ; try solve by inversion ...
  Case "T_Sub".
    destruct IHHty as [s [H1 [H2 H3]]] ...
    eexists ; repeat split ...
Qed.

Lemma abs_arrow : 
  forall x S1 s2 T1 T2 s,
    has_type empty (tm_abs x S1 s2) (arrow T1 T2 s) ->
    subtype T1 S1 /\ has_type (extend empty x S1) s2 T2.
Proof with eauto.
  intros x S1 s2 T1 T2 s Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [H1 H2]].
  apply sub_inversion_arrow in H1.
  destruct H1 as [s' [T1' [T2' [H3 [H4 [H5 H6]]]]]].
  inv H3 ...
Qed.

(** context invariance **)

Inductive appears_free_in : id -> term -> Prop :=
  | afi_var : forall i, appears_free_in i (tm_var i)
  | afi_app1 : forall i t1 t2, appears_free_in i t1 ->
                               appears_free_in i (tm_app t1 t2)
  | afi_app2 : forall i t1 t2, appears_free_in i t2 ->
                               appears_free_in i (tm_app t1 t2)
  | afi_abs : forall i x T t, i <> x -> appears_free_in i t ->
                              appears_free_in i (tm_abs x T t)
  | afi_if1 : forall i t1 t2 t3, appears_free_in i t1 ->
                                 appears_free_in i (tm_if t1 t2 t3)
  | afi_if2 : forall i t1 t2 t3, appears_free_in i t2 ->
                                 appears_free_in i (tm_if t1 t2 t3)
  | afi_if3 : forall i t1 t2 t3, appears_free_in i t3 ->
                                 appears_free_in i (tm_if t1 t2 t3)
  | afi_trust : forall i t, appears_free_in i t ->
                            appears_free_in i (tm_trust t)
  | afi_distrust : forall i t, appears_free_in i t ->
                               appears_free_in i (tm_distrust t)
  | afi_check : forall i t, appears_free_in i t ->
                            appears_free_in i (tm_check t).

Hint Constructors appears_free_in.
  
Lemma context_invariance :
  forall ctx ctx' t S, has_type ctx t S ->
    (forall x, appears_free_in x t -> ctx x = ctx' x) ->
    has_type ctx' t S.
Proof with eauto.
  intros. generalize dependent ctx'.
  has_type_cases (induction H) Case ; intros ctx' Heqv ; try solve by inversion ...
  Case "T_Var".
    apply T_Var. rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs ...
    apply IHhas_type. intros x0 Hafi ; unfold extend.
    remember (beq_id x x0) as e ; destruct e ...
    symmetry in Heqe.
    apply beq_id_false_not_eq in Heqe ...
  Case "T_App".
    eapply T_App ...
  Case "T_If".
    eapply T_If ...
Qed.

Lemma free_in_context :
  forall i ctx t T,
    appears_free_in i t ->
    has_type ctx t T ->
    exists T', ctx i = Some T'.
Proof with eauto.
  intros i ctx t T Hafi Hty.
  has_type_cases (induction Hty) Case ; inv Hafi ...
  Case "T_Abs".
    destruct (IHHty H4) as [T Ht]. exists T. unfold extend in Ht.
    apply not_eq_beq_id_false in H2. rewrite beq_id_sym in H2.
    rewrite H2 in Ht ...
Qed.

(** substitution lemma **)

Hint Resolve typing_inversion_false typing_inversion_true.

Lemma substitution_preserves_typing : 
  forall Gamma x U v t S,
    has_type (extend Gamma x U) t S ->
    has_type empty v U ->
    has_type Gamma (subst x v t) S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S ; generalize dependent Gamma.
  term_cases (induction t) Case ; intros ; simpl.
  Case "tm_false".
     apply typing_inversion_false in Htypt.
     eapply T_Sub...
  Case "tm_true".
     apply typing_inversion_true in Htypt.
     eapply T_Sub ...
  Case "tm_if".
     assert (exists s, has_type (extend Gamma x U) t1 (ty_bool s) /\ 
                       has_type (extend Gamma x U) t2 S /\ 
                       has_type (extend Gamma x U) t3 S)
       by apply (typing_inversion_if _ _ _ _ _ Htypt)...
     destruct H as [s [H1 [H2 H3]]]...
  Case "tm_var".
     destruct (typing_inversion_var _ _ _ Htypt) as [T [H1 H2]].
     unfold extend in H1.
     remember (beq_id x i) as e ; destruct e.
     SCase "x = i".
       apply beq_id_eq in Heqe ; inv H1.
       apply context_invariance with empty ...
       intros x contra.
       destruct (free_in_context _ empty _ T contra) ...      
       inv H.
     SCase "x <> i".
       symmetry in Heqe.
       apply beq_id_false_not_eq in Heqe.
       apply T_Sub with T ...
   Case "tm_app".
     destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [T11 [s [H1 [H2 [H3 H4]]]]]].  
     apply IHt1 in H1.
     apply IHt2 in H2.
     eapply T_Sub.  
     eapply T_App...
     destruct S ; simpl in * ; rewrite <- H4 ...
   Case "tm_abs".
     rename i into y. rename t into T1.
     destruct (typing_inversion_abs _ _ _ _ _ Htypt) as [T2 [H1 H2]].
     apply T_Sub with (arrow T1 T2 Trust)... apply T_Abs...
     remember (beq_id x y) as e ; destruct e.
     SCase "x = y".
       eapply context_invariance ...       
       apply beq_id_eq in Heqe ; subst.
       intros x0 Hafi ; unfold extend.
       destruct (beq_id y x0) ...
     SCase "x <> y".
       apply IHt. eapply context_invariance ...
       intros z Hafi. unfold extend.
       remember (beq_id y z) as e1 ; destruct e1...
       apply beq_id_eq in Heqe1. subst. rewrite <- Heqe ...
   Case "tm_trust".
     destruct (typing_inversion_trust _ _ _ Htypt) as [T [H1 H2]].
     apply T_Sub with (update_secty T Trust) ...
   Case "tm_distrust".
     destruct (typing_inversion_distrust _ _ _ Htypt) as [T [H1 H2]].
     apply T_Sub with (update_secty T Untrust) ...
   Case "tm_check".
     destruct (typing_inversion_check _ _ _ Htypt) as [T [H1 [H2 H3]]].
     eapply T_Sub...
Qed.
     
(** preservation **)

Theorem preservation : 
  forall t t' T, has_type empty t T ->
    t ==> t' -> has_type empty t' T.
Proof with eauto.
 intros t t' T HT.
 remember (@empty ty) as ctx. generalize dependent Heqctx.
 generalize dependent t'.
 has_type_cases (induction HT) Case ; intros t' Heqctx HE ; inv HE...
 Case "T_App".
   SCase "ST_AppAbs".
     destruct (abs_arrow _ _ _ _ _ _ HT1) as [HA1 HA2].
     apply substitution_preserves_typing with T ...
Qed.