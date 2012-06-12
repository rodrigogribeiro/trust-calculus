(** Implementation of a typechecker for
    the trust calculus **)

Require Import SfLib Tactics Syntax TypeSystem Subtype.
Require Import Wf Wellfounded.Lexicographic_Product.
Require Import Relation_Operators Transitive_Closure Recdef Program MinMax.
Require Import Ty.


(** security type ordering is decidable **)

Definition sec_ordering_dec : forall (s s' : secty), {sec_ordering s s'} + {~ sec_ordering s s'}.
   refine (
     fun (s s' : secty) => 
         match s, s' with
           | Trust, Untrust => _
           | Untrust, DontCare => _
           | Trust, DontCare => _
           | DontCare ,DontCare => _
           | _ , _ => _
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
       end) ; eauto.

Obligation Tactic := try my_tac ; (simpl ; omega).

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

