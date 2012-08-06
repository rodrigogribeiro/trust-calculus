(** Utils.v 
    Some utilities that are used in several places.
**)

Require Export Bool.
Require Export List.
Require Export Arith_base.
Require Export Arith.EqNat.

(** case tactic **)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(** inv and solve by inversion tactic **)

Ltac inv H := inversion H ; clear H ; subst.


Tactic Notation "solve_by_inversion_step" tactic(t) :=
  (match goal with
    | H : _ |-  _ => solve [ inversion H; subst; t ]
    end) || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(** notations for easy working with subset types **)

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _  (exist _ x _) ).

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).

(** identifiers **)

Inductive id : Type :=
  | Id : nat -> id.

Definition lt_id (i i' : id) : Prop :=
  match i, i' with
    | Id n, Id n' => lt n n'
  end.

Definition beq_id (i i' : id) : bool :=
  match i, i' with
    | Id n, Id n' => beq_nat n n'
  end.

Lemma beq_id_false_not_eq : forall i i', beq_id i i' = false -> i <> i'.
Proof.
  intros i i'.
  destruct i ; destruct i'.
  intros H1 H2. inv H2.
  simpl in H1. apply beq_nat_false in H1 ; elim H1 ; auto.
Qed.

Lemma beq_id_true_eq : forall i i', beq_id i i' = true -> i = i'.
Proof.
  intros i i' H. destruct i ; destruct i' ; f_equal ; simpl in H.
  apply beq_nat_true ; auto.
Qed.

Definition eq_id_dec : forall (i i' : id), {i = i'} + {i <> i'}.
   pose eq_nat_dec.
   decide equality.
Defined.

Lemma eq_id_refl : forall (i : id), i = i.
Proof.
  auto.
Qed.

Lemma eq_id_sym : forall (i1 i2 : id), i1 = i2 -> i2 = i1.
Proof.
  intros ; symmetry ; auto.
Qed.

Lemma eq_id_trans : forall (i1 i2 i3 : id), i1 = i2 -> i2 = i3 -> i1 = i3.
Proof.
  intros i1 i2 i3 H1 H2. rewrite -> H1. auto.
Qed.

Lemma lt_id_trans : forall (i1 i2 i3 : id), lt_id i1 i2 -> lt_id i2 i3 -> lt_id i1 i3.
Proof.
  intros i1 i2 i3 H1 H2.
  destruct i1 ; destruct i2 ; destruct i3 ; simpl in *.
  eapply lt_trans ; eauto.
Qed.

Lemma lt_id_not_eq_id : forall (i1 i2 : id), lt_id i1 i2 -> i1 <> i2.
Proof.
  intros i1 i2 H. destruct i1 ; destruct i2 ; intro contra.
  rewrite -> contra in H. simpl in H.
  apply lt_irrefl in H ; auto.
Qed.

Definition lt_eq_lt_id_dec (i1 i2 : id) : {lt_id i1 i2} + {i1 = i2} + {lt_id i2 i1}.
   refine (match i1,i2 with 
             Id n1, Id n2 => match lt_eq_lt_dec n1 n2 with
                               | inleft _ => _
                               | inright _ => match lt_dec n2 n1 with
                                                | left _ => _
                                                | right _ => _
                                              end
                             end
           end).
  destruct s. left ; left ; auto.
  subst ; left ; right ; auto.
  right ; auto.
  contradiction.
Defined. 

(** definitions of reflexive-transitive closure of a relation **)

Definition relation (X: Type) := X -> X -> Prop.

Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
  | rsc_refl : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

Hint Constructors refl_step_closure.

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y r.
  apply rsc_step with y. apply r. apply rsc_refl.   Qed.

Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  intros X R x y z H1.
  induction H1. trivial.
  intros H2.
  apply IHrefl_step_closure in H2.
  eapply rsc_step ; eassumption ; eauto.
Qed.

Theorem ex_falso_quodlibet : forall (P:Type),
  False -> P.
Proof.
  intros P contra.
  inversion contra. Qed.



