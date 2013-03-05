(** Implementation of a typechecker for
    the trust calculus **)

Require Import Utils Context Tactics Syntax TypeSystem Subtype.
Require Import Wf Wellfounded.Lexicographic_Product Coq.Program.Tactics Omega.
Require Import Relation_Operators Transitive_Closure Recdef Program.
Require Import Ty.


(** security type ordering is decidable **)

Definition sec_ordering_dec : forall (s s' : secty), {sec_ordering s s'} + {~ sec_ordering s s'}.
   refine (
     fun (s s' : secty) => 
         match s, s' with
           | Trust, Untrust => _
           | Untrust, Trust => _
           | Trust, Trust => _
           | Untrust, Untrust => _
        end
    ) ; auto ; right ; intro H ; try solve by inversion.
Defined.

(** subtype relation is decidable **)

Definition typair_size (t t' : ty) := ty_size t + ty_size t'.

Ltac my_tac :=
  unfold typair_size ; intuition ; simpl in *; try subst ;
  try (match goal with
         | [H : subtype _ _ |- _] => inv H ; try contradiction
         | [H : arrow _ _ _ = ty_bool _ |- _] => inv H
         | [H : ty_bool _ = arrow _ _ _ |- _] => inv H
         | [|- _ /\ _] => split
         | [H : ex _ |- _] => destruct H
         | [H : Some _ = Some _ |- _] => inv H
         | [H : None = Some _ |- _] => congruence
         | [H : ?X -> False |- False] => apply H
       end) ; eauto.

Ltac s := try (repeat my_tac) ; (simpl ; try omega).

Obligation Tactic := s.

Program Fixpoint subtype_dec (t t' : ty) {measure (typair_size t t')} : {subtype t t'} + {~ subtype t t'} :=
  match t,t' with
    | ty_bool s, ty_bool s'
      => if sec_ordering_dec s s' then left _ else right _
    | arrow l r s, arrow l' r' s'
      => match (subtype_dec l' l), (subtype_dec r r'), sec_ordering_dec s s' with 
            | left _, left _, left _ => left _
            | left _  , left _ , right _ => right _ 
            | left _ , right _ , left _ => right _
            | left _ , right _, right _ => right _
            | right _, left _, left _ => right _
            | right _, left _, right _ => right _
            | right _, right _, left _ => right _
            | right _, right _, right _ => right _
         end
    | _, _ => right _
  end.

Definition trustworth (t : ty) : {sectyof t = Trust} + {~ sectyof t = Trust}.
  decide equality.
Defined.

(** Defining the typechecker itself **)  


Ltac start := 
     repeat
       (match goal with
         | [H : forall _, _ |- _] => intro ; start
         | [H : ~ _ |- _] => intro ; clear H
         | [H : ex _ |- _] => destruct H
         | [|- has_type_alg _ _ _] => econstructor (solve [eauto])
         | [H : (ty * ty)%type |- _] => destruct H
       end ; try subst ; simpl) ; eauto.

Definition var_dec : forall i (ctx : finite_map ty), {t | lookup i ctx = Some t} + {~ exists t, lookup i ctx = Some t}.
  intros i ctx.
  destruct (lookup i ctx) ; [left ; eexists | right ; intro] ; eauto.
  destruct H. inv H.
Defined.

Definition arrow_split (t : ty) : {(t1,t2) : ty * ty | exists s, t = arrow t1 t2 s} + 
                                  {~ (exists t1, exists t2, exists s, t = arrow t1 t2 s)}.
  destruct t.
  right. intro H. destruct H as [t1 [t2 [s' H]]] ; inv H.
  left . exists (t1,t2). exists s. auto.
Defined. 

Definition is_a_bool_ty : forall (t : ty), {exists s, subtype t (ty_bool s)} + 
                                           {~ exists s, subtype t (ty_bool s)}.
   intros t ; destruct t.
   left. destruct s ; [exists Trust | exists Untrust] ; auto.
   right. intro H. destruct H as [s1 H1] ; inv H1.
Defined.

Definition typecheck_dec : forall(e : term) (ctx : finite_map ty), 
  {t | has_type_alg ctx e t} + {forall t, ~ has_type_alg ctx e t}.
  refine (fix F (e : term) (ctx : finite_map ty) {struct e}: 
     {t | has_type_alg ctx e t} + {forall t, ~ has_type_alg ctx e t} :=
     match e return {t | has_type_alg ctx e t} + {forall t, ~ has_type_alg ctx e t} with
       | tm_true => [|| (ty_bool Trust) ||]
       | tm_false => [|| (ty_bool Trust) ||]
       | tm_var i => 
           match var_dec i ctx with
             | inleft (exist t _) => [|| t ||]
             | inright _ => !!
           end
       | tm_abs i ty e =>
            ty' <-- F e (extend i ty ctx) ;
            [|| arrow ty ty' Trust ||]
       | tm_app l r => 
            tf <-- F l ctx ;
            ta <-- F r ctx ;
            p  <-- arrow_split tf ;
            subtype_dec ta (fst p) ;;;
            [|| update_secty (snd p) (sectyof tf) ||]
       | tm_trust t  => 
            ty <-- F t ctx ;
            [|| update ty Trust ||]
       | tm_distrust t => 
            ty <-- F t ctx ;
            [|| update ty Untrust ||]
       | tm_check t => 
            ty <-- F t ctx ;
            trustworth ty ;;;
            [|| ty ||]
     end) ; start. 
     elim n ; inv H ; eexists ; eauto.
     simpl in *.
     destruct s1 as [[t2 t3] [s' He]] ; inv He.
     inv H.
     apply (has_type_alg_unique _ _ _ H2) in h ; inv h.
     apply (has_type_alg_unique _ _ _ h0) in H4 ; inv H4.
     contradiction.
     inv H ; elim n. 
     apply (has_type_alg_unique _ _ _ H2) in h ; inv h.
     exists T11 ; exists T12 ; exists s1 ; auto.
     inv H ; apply n in H4 ; auto.
     inv H ; apply n in H2 ; auto.
     inv H ; apply n in H5 ; auto.
     inv H ; apply n in H2 ; auto.
     inv H ; apply n in H2 ; auto.
     inv H.
     apply (has_type_alg_unique _ _ _ h) in H1 ; subst.
     contradiction.
     inv H. apply n in H1 ; auto.
 Defined.

