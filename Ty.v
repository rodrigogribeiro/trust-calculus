(** Definition of type syntax and related definitions **)

Require Import Utils.

(* definition of a trust annotation *)

Inductive secty : Type := Trust : secty | Untrust : secty.

(* decidable equality on trust annotations *)

Definition secty_eq_dec : forall (s s' : secty), {s = s'} + {s <> s'}.
  decide equality.
Defined.

(* definition of type syntax. 
   We only consider a base type: bool.
   Each type must have its trust annotation *)
  
Inductive ty : Type :=
  | ty_bool : secty -> ty
  | arrow : ty -> ty -> secty -> ty.

(* decidable equality for types *)

Definition ty_eq_dec : forall (t t' : ty), {t = t'} + {t <> t'}.
  pose secty_eq_dec.
  decide equality.
Defined.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first ; [Case_aux c "base" | Case_aux c "arrow"].

(** definition of a type size,
    this is used to ensure termination
    of subtyping algorithm **)

Fixpoint ty_size (T : ty) : nat :=
  match T with
    | arrow l r _ => 1 + (ty_size l) + (ty_size r)
    | _           => 0
  end.
