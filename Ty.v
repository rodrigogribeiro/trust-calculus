(** Definition of types **)

Require Import SfLib.

Inductive secty : Type := Trust : secty | Untrust : secty | DontCare : secty.

Definition secty_eq_dec : forall (s s' : secty), {s = s'} + {s <> s'}.
  decide equality.
Defined.
  
Inductive ty : Type :=
  | ty_bool : secty -> ty
  | arrow : ty -> ty -> secty -> ty.

Definition ty_eq_dec : forall (t t' : ty), {t = t'} + {t <> t'}.
  pose secty_eq_dec.
  pose eq_id_dec.
  decide equality.
Defined.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first ; [Case_aux c "base" | Case_aux c "arrow"].

Definition context := partial_map ty.