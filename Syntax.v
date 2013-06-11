
(* Definition of the syntax of the trust lambda-calculus *)

Require Import Utils Ty.

Inductive term : Type :=
  | tm_false : term
  | tm_true : term
  | tm_var : id -> term
  | tm_app : term -> term -> term
  | tm_abs : id -> ty -> term -> term
  | tm_trust : term -> term
  | tm_distrust : term -> term
  | tm_check : term -> term.

Tactic Notation "term_cases" tactic(first) ident(c) :=
  first ; [Case_aux c "tm_false" | Case_aux c "tm_true" | 
           Case_aux c "tm_var" | Case_aux c "tm_app"  | Case_aux c "tm_abs" |
           Case_aux c "tm_trust" | Case_aux c "tm_distrust" | Case_aux c "tm_check"].
