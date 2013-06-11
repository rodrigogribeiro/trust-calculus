
Require Import Utils Context Syntax Ty Subtype Semantics.

(** Definition of the type system -- non syntax directed version**)

Inductive has_type : finite_map ty -> term -> ty -> Prop :=
  | T_True : forall ctx, has_type ctx tm_true (ty_bool Trust)
  | T_False : forall ctx, has_type ctx tm_false (ty_bool Trust)
  | T_Var : forall ctx v ty, 
               lookup v ctx = Some ty -> has_type ctx (tm_var v) ty
  | T_Abs : forall ctx x t2 T1 T2, 
        has_type (extend x T1 ctx) t2 T2 ->
        has_type ctx (tm_abs x T1 t2) (arrow T1 T2 Trust)
  | T_App : forall ctx t1 t2 T11 T12 s, 
        has_type ctx t1 (arrow T11 T12 s) -> 
        has_type ctx t2 T11 ->
        has_type ctx (tm_app t1 t2) (update_secty T12 s)
  | T_Trust : forall ctx t T,
        has_type ctx t T ->
        has_type ctx (tm_trust t) (update T Trust)
  | T_Untrust : forall ctx t T,
        has_type ctx t T ->
        has_type ctx (tm_distrust t) (update T Untrust)
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
           Case_aux c "T_Abs"   | Case_aux c "T_App"     | Case_aux c "T_Trust" | 
           Case_aux c "T_Untrust" | Case_aux c "T_Check" | Case_aux c "T_Sub"].

Hint Constructors has_type.

(** inversion lemmas for subtyping **)

Lemma sub_inversion_base : 
  forall T s, subtype T (ty_bool s) -> exists s', sec_ordering s' s /\ T = (ty_bool s').
Proof with eauto.
  intros T s Hsub.
  remember (ty_bool s) as V.
  subtype_cases (induction Hsub) Case ; try (inv HeqV) ; try (eexists ; split ; eauto).
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
  has_type_cases (induction Hty) Case ; try intros ; try solve by inversion 2.
  left ... right ... subst.
  apply sub_inversion_base in H.
  destruct H as [s' [Heq Hs]].
  eapply IHHty ...
Qed.

(** inversion lemmas for the typing relation *)

Lemma typing_inversion_abs : 
  forall ctx x S1 s2 T, has_type ctx (tm_abs x S1 s2) T ->
    exists S2,  subtype (arrow S1 S2 Trust) T /\
      has_type (extend x S1 ctx) s2 S2.
Proof with eauto.
  intros ctx x S1 s2 T H.
  remember (tm_abs x S1 s2) as t.
  has_type_cases (induction H) Case ; inv Heqt ; intros ; try solve by inversion.
  Case "T_Abs".
    exists T2 ; split ...   
  Case "T_Sub".
    destruct IHhas_type as [S2 [H1 H2]] ; repeat (eexists ; split ; eauto).
Qed.

Lemma typing_inversion_var : 
  forall ctx x T, has_type ctx (tm_var x) T ->
    exists S, lookup x ctx = Some S /\ subtype S T.
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
    exists T1, exists s, 
      has_type ctx t1 (arrow T1 T2 s) /\ has_type ctx t2 T1 /\ sectyof T2 = sectyof (update_secty T2 s).
Proof with eauto.
  intros ctx t1 t2 T2 Hty.
  remember (tm_app t1 t2) as t.
  has_type_cases (induction Hty) Case ; intros ; inv Heqt ; try solve by inversion ...
  Case "T_App".
    repeat eexists...
    rewrite <- update_secty_ident ...
  Case "T_Sub".
    destruct IHHty ...
    destruct H0 as [s1 [H1 [H2 H3]]].
    repeat eexists ... eapply secty_update_eq ...
Qed.

Lemma typing_inversion_trust : 
  forall ctx t T, has_type ctx (tm_trust t) T ->
    exists T', has_type ctx t T' /\ subtype (update T' Trust) T.
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
    exists T', has_type ctx t T' /\ subtype (update T' Untrust) T.
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

Lemma abs_arrow : 
  forall x S1 s2 T1 T2 s,
    has_type empty (tm_abs x S1 s2) (arrow T1 T2 s) ->
    subtype T1 S1 /\ has_type (extend x S1 empty) s2 T2.
Proof with eauto.
  intros x S1 s2 T1 T2 s Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [H1 H2]].
  apply sub_inversion_arrow in H1.
  destruct H1 as [s' [T1' [T2' [H3 [H4 [H5 H6]]]]]].
  inv H3 ...
Qed.

(** progress *)

Theorem progress : 
  forall t T, has_type empty t T ->
    value t \/ untrust_value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Hty.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Hty) Case ; 
  intros Heq ; subst ; try solve by inversion 2 ; try (left ; eauto ; fail)...
  Case "T_App".
    right. right.
    destruct IHHty1 ; subst ...
    SCase "t1 is a value".
      destruct IHHty2 ; subst ...
      SSCase "t2 is a value".
        destruct (canonical_forms_arrows empty t1 T11 T12 s) 
          as [x [S1 [s2 Heq]]] ... subst. 
        exists (subst x t2 s2)...
      destruct H0.
      SSCase "t2 is untrust value".
         destruct (canonical_forms_arrows empty t1 T11 T12 s) as [x [S1 [s2 Heq]]] ; subst ...
      SSCase "t2 can step".
         destruct H0 as [t2' H1]. exists (tm_app t1 t2')...
    destruct H.
    SCase "t1 is an untrust value".
      destruct H as [t1' Ht1']. inv Ht1'.
      apply typing_inversion_distrust in Hty1.
      destruct Hty1 as [T [HT HS]].
      apply sub_inversion_arrow in HS. destruct HS as [s' [T1' [T2' [He [Hs1 [Hs2 Hss]]]]]].
      destruct T. inv He. simpl in He ; inv He. apply typing_inversion_true in HT. inv HT.
      apply typing_inversion_distrust in Hty1.
      destruct Hty1 as [T [HT HS]].
      apply sub_inversion_arrow in HS. destruct HS as [s' [T1' [T2' [He [Hs1 [Hs2 Hss]]]]]].
      destruct T. inv He. simpl in He ; inv He. apply typing_inversion_false in HT. inv HT.
      destruct IHHty2 ... destruct H.
      exists (tm_distrust (subst x t2 t))...
      destruct H as [t2' H].
      exists (tm_app (tm_distrust (tm_abs x T t)) t2') ...
      SCase "t1 can step".
         destruct H as [t1' Ht1']. exists (tm_app t1' t2) ...
  Case "T_Trust".
    destruct IHHty... destruct H. inv H. right. right.
    exists (tm_trust v) ...
    destruct H as [t' Ht'] ; right ; right ; exists (tm_trust t') ...
  Case "T_Untrust".
    destruct IHHty ... destruct H.
    inv H. right ; right. exists (tm_distrust v). apply e_distrustd1...
    destruct H as [t' Ht'] ; right ; right ; exists (tm_distrust t') ...
  Case "T_Check".
    destruct IHHty ... destruct H0.
    inv H0. apply typing_inversion_distrust in Hty. destruct Hty as [T' [HT' HS]]. 
    apply subtype_untrust_secty in HS... rewrite H in HS ; inv HS... 
    destruct T' ; simpl ...
    destruct H0 as [t' Ht'] ; right ; right ; exists (tm_check t') ...
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
  | afi_trust : forall i t, appears_free_in i t ->
                            appears_free_in i (tm_trust t)
  | afi_distrust : forall i t, appears_free_in i t ->
                               appears_free_in i (tm_distrust t)
  | afi_check : forall i t, appears_free_in i t ->
                            appears_free_in i (tm_check t).

Hint Constructors appears_free_in.

Definition closed (t : term) := ~ (exists v, appears_free_in v t).
  
Lemma context_invariance :
  forall ctx ctx' t S, has_type ctx t S ->
    (forall x, appears_free_in x t -> lookup x ctx = lookup x ctx') ->
    has_type ctx' t S.
Proof with eauto.
  intros ctx ctx' t S H. generalize dependent ctx'.
  has_type_cases (induction H) Case ; intros ctx' Heqv ; try solve by inversion ...
  Case "T_Var".
    apply T_Var. rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs ...
    apply IHhas_type. intros x0 Hafi.
    remember (beq_id x x0) as e ; destruct e ...
    symmetry in Heqe.
    apply beq_id_true_eq in Heqe ...
    subst.
    rewrite extend_lookup ; rewrite extend_lookup ; auto.
    symmetry in Heqe. apply beq_id_false_not_eq in Heqe.
    assert (x0 <> x). intro Hc ; unfold not in Heqe ; symmetry in Hc ; contradiction.
    apply extend_lookup_neq with (g := ctx) (t := T1) in H0.
    rewrite H0.
    assert (x0 <> x). intro Hc ; unfold not in Heqe ; symmetry in Hc ; contradiction.
    apply extend_lookup_neq with (g := ctx') (t := T1) in H1.
    rewrite H1 ; auto.
  Case "T_App".
    eapply T_App ...
Qed.

Lemma free_in_context :
  forall i ctx t T,
    appears_free_in i t ->
    has_type ctx t T ->
    exists T', lookup i ctx = Some T'.
Proof with eauto.
  intros i ctx t T Hafi Hty.
  has_type_cases (induction Hty) Case ; inv Hafi ...
  Case "T_Abs".
    destruct (IHHty H4) as [T Ht]. exists T.
    apply extend_lookup_neq with (t := T1) (g := ctx) in H2.
    rewrite H2 in Ht ...
Qed.


Corollary typable_empty__closed : forall t T,
    has_type empty t T ->
    closed t.
Proof.
  intros t T H. unfold closed. intros H1 ; destruct H1 as [x H2].
  destruct (free_in_context _ _ _ _ H2 H) as [T' C].
  inversion C. Qed.

(** substitution lemma **)

Hint Resolve typing_inversion_false typing_inversion_true.

Lemma substitution_preserves_typing : 
  forall Gamma x U v t S,
    has_type (extend x U Gamma) t S ->
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
  Case "tm_var".
     destruct (typing_inversion_var _ _ _ Htypt) as [T [H1 H2]].
     remember (beq_id x i) as e ; destruct e.
     SCase "x = i".
       symmetry in Heqe.
       apply beq_id_true_eq in Heqe. subst.
       rewrite extend_lookup in H1. inv H1.
       apply T_Sub with (T := T)...
       apply context_invariance with empty ...
       intros x contra.       
       destruct (free_in_context _ empty _ T contra) ; try solve by inversion...      
     SCase "x <> i".
       symmetry in Heqe.
       apply beq_id_false_not_eq in Heqe.
       apply context_invariance with (extend x U Gamma)...
       intros x1 contra. inv contra.
       apply extend_lookup_neq. 
       intro Hc ; symmetry in Hc ; unfold not in Heqe ; contradiction.
   Case "tm_app".
     destruct (typing_inversion_app _ _ _ _ Htypt) as [T [s [H1 [H2 H3]]]].
     apply IHt1 in H1.
     apply IHt2 in H2.
     eapply T_Sub.  
     eapply T_App...
     destruct S ; simpl in * ; rewrite <- H3 ...
   Case "tm_abs".
     rename i into y. rename t into T1.
     destruct (typing_inversion_abs _ _ _ _ _ Htypt) as [T2 [H1 H2]].
     apply T_Sub with (arrow T1 T2 Trust)... apply T_Abs...
     remember (beq_id x y) as e ; destruct e.
     SCase "x = y".
       eapply context_invariance ...       
       symmetry in Heqe. apply beq_id_true_eq in Heqe ; subst.
       intros x0 Hafi.
       destruct (beq_id y x0) ...
       rewrite extend_override ...
       rewrite extend_override...
     SCase "x <> y".
       apply IHt. eapply context_invariance ...
       intros z Hafi. symmetry in Heqe. apply beq_id_false_not_eq in Heqe.
       remember (beq_id y z) as e1 ; destruct e1...
       eapply extend_swap_neq in Heqe ...
       symmetry in Heqe1. apply beq_id_false_not_eq in Heqe1. 
       eapply extend_swap_neq in Heqe ...
   Case "tm_trust".
     destruct (typing_inversion_trust _ _ _ Htypt) as [T [H1 H2]].
     apply T_Sub with (update T Trust) ...
   Case "tm_distrust".
     destruct (typing_inversion_distrust _ _ _ Htypt) as [T [H1 H2]].
     apply T_Sub with (update T Untrust) ...
   Case "tm_check".
     destruct (typing_inversion_check _ _ _ Htypt) as [T [H1 [H2 H3]]].
     eapply T_Sub...
Qed.
     
(** preservation **)

Remark update_arrow : forall T T1 T2 s s', update T s = arrow T1 T2 s' -> exists s1, T = arrow T1 T2 s1 /\ s = s'.
Proof.
  intros T T1 T2 s s' H1.
  induction T ; simpl in * ; try solve by inversion.
  inv H1.
  exists s0 ; split ; auto. 
Qed.

Remark subtype_untrust : forall T, subtype T (update T Untrust).
Proof.
  induction T ; simpl ; destruct s ; auto.
Qed.

Remark subtype_trust : forall T, subtype (update T Trust) T.
Proof.
  induction T ; simpl ; destruct s ; auto.
Qed.

Remark subtype_trust1 : forall T T', sectyof T = Trust -> subtype T' T -> subtype T' (update T Trust).
Proof.
  intros T T' H H1 ; induction H1 ; simpl in * ; subst ; auto.
Qed.

Remark sectyof_update : forall T s, sectyof (update T s) = s.
Proof.
  induction T ; auto.
Qed.

Remark update_preserves_subtype : forall T T' s, subtype T T' -> subtype (update T s) (update T' s).
Proof.
  induction 1 ; simpl in * ; auto.
Qed.

Remark subtype_update1 : forall T s, sec_ordering Untrust s -> subtype (update T Untrust) (update_secty T s).
Proof.
  induction T ; intros s' H ; simpl ; inv H ; auto.
Qed.


Hint Resolve subtype_untrust sectyof_update subtype_trust subtype_trust1 
             update_preserves_subtype subtype_update1.

Theorem preservation : 
  forall t t' T, has_type empty t T ->
    t ==> t' -> exists T', has_type empty t' T' /\ subtype T' T.
Proof with eauto.
 intros t t' T HT ;
   remember (@empty ty) as ctx ; generalize dependent t' ;
     has_type_cases (induction HT) Case ; intros t' HE ; inv HE...
  Case "T_App".
     destruct (abs_arrow _ _ _ _ _ _ HT1) as [HA1 HA2].
     exists (update_secty T12 s) ; split.
     eapply substitution_preserves_typing with T...
     apply subtype_refl.
     destruct (IHHT1 eq_refl t1' H2) as [Ta [HTa HSa]].
     destruct (sub_inversion_arrow _ _ _ _ HSa) as [sa [Ta1 [Ta2 [Ha1 [Ha2 [Ha3 Ha4]]]]]] ; subst.
     exists (update_secty T12 s) ; split ...
     destruct (IHHT2 eq_refl t2' H3) as [Ta [HTa HSa]].
     exists (update_secty T12 s) ; split ...
     exists (update_secty T12 s) ; split ...
     destruct (abs_arrow _ _ _ _ _ _ HT1) as [HA1 HA2].
     eapply substitution_preserves_typing with T...
     destruct (IHHT2 eq_refl t2' H3) as [Ta [HTa HSa]].
     exists (update_secty T12 s) ; split ...
     destruct (typing_inversion_distrust _ _ _ HT1) as [Ta [HTa HSa]].
     destruct (sub_inversion_arrow _ _ _ _ HSa) as [sa [Ta1 [Ta2 [Ha1 [Ha2 [Ha3 Ha4]]]]]] ; subst.
     apply update_arrow in Ha1. destruct Ha1 as [sx [Hx1 Hx2]]. subst. simpl in *.
     exists (update T12 Untrust) ; split... apply T_Untrust.
     destruct (typing_inversion_abs _ _ _ _ _ HTa) as [Tc [HSc HTc]].
     inv HSc. apply (subtype_trans _ _ _ H7) in Ha3.
     apply substitution_preserves_typing with T...
     inv HT1. apply update_arrow in H1. destruct H1 as [sb [Hb Hb']].
     subst.
     exists (update T12 Untrust) ; split ... apply T_Untrust.
     inv H3.
     apply substitution_preserves_typing with T11...
     destruct (typing_inversion_abs _ _ _ _ _ H) as [Td [HSd HTd]].
     inv HSd. inv H0. apply (subtype_trans _ _ _ H7) in H12.
     apply substitution_preserves_typing with T...
     destruct (typing_inversion_distrust _ _ _ H) as [Ta [HTa HSa]].
     destruct (typing_inversion_abs _ _ _ _ _ HTa) as [Tb [HSb HTb]].
     destruct (sub_inversion_arrow _ _ _ _ H0) as [sc [Tc1 [Tc2 [Hc1 [Hc2 [Hc3 Hc4]]]]]] ; subst.
     destruct (sub_inversion_arrow _ _ _ _ HSa) as [sd [Td1 [Td2 [Hd1 [Hd2 [Hd3 Hd4]]]]]] ; subst.
     destruct (update_arrow _ _ _ _ _ Hd1) as [se [He1 He2]]. subst. simpl in *.
     inv HSa. clear Hd1. inv Hd4 ; clear H10. inv Hc4.
     exists (update T12 Untrust) ; split ... apply T_Untrust. inv H0.
     inv HSb. simpl. apply substitution_preserves_typing with T... 
 Case "T_Trust".
     destruct (IHHT eq_refl t1' H0) as [Ta [HTa HSa]].
     exists (update T Trust) ; split ...
     destruct (typing_inversion_distrust _ _ _ HT) as [Ta [HTa HSa]].
     exists (update T Trust) ; split ...
     exists (update T Trust) ; split ...
     inv H0. apply typing_inversion_true in HT.
     destruct T. simpl in *. apply T_True. inv HT.
     apply typing_inversion_false in HT. destruct T ; simpl in *...
     inv HT.
     destruct (typing_inversion_abs _ _ _ _ _ HT) as [T1 [Ha1 Ha2]].
     inv Ha1. simpl.
     apply T_Sub with (arrow T0 T2' Trust). apply T_Abs ...
     constructor ...
 Case "T_Untrust".
     destruct (IHHT eq_refl t1' H0) as [T' [HT' HS']].
     exists (update T' Untrust) ; split ...
 Case "T_Check".
     destruct (IHHT eq_refl t1' H1) as [T' [HT' HS']].
     exists (update T Trust) ; split...
 Case "T_Sub".
     destruct (typing_inversion_app _ _ _ _ HT) as [T1 [s1 [HA1 [HA2 HA3]]]].
     destruct (IHHT eq_refl (subst x v2 t12)) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_app t1' t2)) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_app v1 t2')) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (subst x v t12)) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_app v1 t2')) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_trust t1')) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_distrust t1')) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_check t1')) as [TH [HB HSB]]...
     destruct (IHHT eq_refl (tm_trust v)) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_distrust v)) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_distrust (subst x v t0))) as [TB [HB HSB]]...
     destruct (IHHT eq_refl (tm_distrust (subst x v t0))) as [TB [HB HSB]]...
     destruct (IHHT eq_refl t') as [TB [HB HSB]]...
     destruct (IHHT eq_refl t') as [TB [HB HSB]]...
Qed.

Definition stuck (t : term) : Prop :=
  (normal_form step) t /\ ~ value t /\ ~ untrust_value t.

Corollary soundness : forall t t' T,
  has_type empty t T ->
  t ==>* t' ->
  ~(stuck t').
Proof with eauto.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf [Hnot_val Hnotu]]. unfold normal_form in Hnf.
  induction Hmulti.
  destruct (progress _ _ Hhas_type) as [Hv | [Hu | He]] ; try contradiction.
  apply IHHmulti ; eauto.
  eapply preservation in Hhas_type ; eauto.
  destruct Hhas_type as [Tx [Hx Hsx]] ; eapply T_Sub...
Qed.

(** syntax directed system **)

Inductive has_type_alg : finite_map ty -> term -> ty -> Prop :=
  | TA_True : forall ctx, has_type_alg ctx tm_true (ty_bool Trust)
  | TA_False : forall ctx, has_type_alg ctx tm_false (ty_bool Trust)
  | TA_Var : forall ctx v ty, 
        lookup v ctx = Some ty -> has_type_alg ctx (tm_var v) ty
  | TA_Abs : forall ctx x t2 T1 T2, 
        has_type_alg (extend x T1 ctx) t2 T2 ->
        has_type_alg ctx (tm_abs x T1 t2) (arrow T1 T2 Trust)
  | TA_App : forall ctx t1 t2 T11 T11' T12 s, 
        has_type_alg ctx t1 (arrow T11 T12 s) -> 
        has_type_alg ctx t2 T11' ->
        subtype T11' T11     ->
        has_type_alg ctx (tm_app t1 t2) (update_secty T12 s)
  | TA_Trust : forall ctx t T,
        has_type_alg ctx t T ->
        has_type_alg ctx (tm_trust t) (update T Trust)
  | TA_Untrust : forall ctx t T,
        has_type_alg ctx t T ->
        has_type_alg ctx (tm_distrust t) (update T Untrust)
  | TA_Check : forall ctx t T,
        has_type_alg ctx t T ->
        sectyof T = Trust ->
        has_type_alg ctx (tm_check t) T. 

Hint Constructors has_type_alg.

Theorem has_type_alg_soundness : 
  forall ctx t ty, has_type_alg ctx t ty -> has_type ctx t ty.
Proof.
  intros ctx t ty H ; induction H ; eauto.
Qed.

Theorem has_type_alg_completeness : 
  forall ctx t ty, has_type ctx t ty -> exists ty', has_type_alg ctx t ty' /\ subtype ty' ty.
Proof with eauto.
  Hint Resolve update_secty_mono.
  intros ctx t ty H ; has_type_cases (induction H) Case ; try (eexists ; split ; eauto ; fail).
  Case "T_Abs".
    destruct IHhas_type as [T [HT HS]].
    apply TA_Abs in HT ; eexists ; split ...
  Case "T_App".
    destruct IHhas_type1 as [T1 [HT1 HS1]].
    destruct IHhas_type2 as [T2 [HT2 HS2]].
    apply sub_inversion_arrow in HS1. destruct HS1 as [s1 [T1' [T2' [HE [HS1' [HS2' HS3]]]]]] ; subst.
    eexists ; split ...
  Case "T_Trust".
    destruct IHhas_type as [T' [HT' HS]].
    eexists ; split ...     
  Case "T_Untrust".
    destruct IHhas_type as [T' [HT' HS]].
    eexists ; split ...
  Case "T_Check".
    destruct IHhas_type as [T' [HT' HS]].
    eexists ; split ; try constructor ... 
  Case "T_Sub".
    destruct IHhas_type as [T1 [HT1 HS]].
    eexists ; split ...
Qed.

Theorem has_type_alg_unique : 
  forall ctx t T, has_type_alg ctx t T -> forall T', has_type_alg ctx t T' -> T = T'.
Proof with eauto.
  intros ctx t T HT ; induction HT ; intros T' HT' ; inv HT' ; auto.
  rewrite H in H2 ; inv H2 ; auto.
  apply IHHT in H4 ; subst ; auto.
  apply IHHT1 in H2 ; inv H2 ; auto.
  apply IHHT in H1 ; subst ; auto.
  apply IHHT in H1 ; subst ; auto.
Qed.
