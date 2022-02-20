Require Import Setoid.

Definition one := unit.
Definition zero := Empty_set.

Definition hProp P := forall a b : P, a = b.

Lemma one_hProp : hProp one.
Proof. intros a; case a. intros b; case b. reflexivity. Qed.

Lemma zero_hProp : hProp zero.
Proof. intros a; case a. Qed.

Inductive eq_true : bool -> Type := is_eq_true : eq_true true.

Coercion eq_true : bool >-> Sortclass.

Notation "! x" := (negb x) (at level 75, right associativity).

Definition false_elim (A:Type) : false -> A :=
  fun F => match F in eq_true false return A with
  end.

Lemma negb_spec : forall (P : bool), !P <-> ~P.
Proof. split; case P; easy. Qed.

Lemma prod_hProp A B : hProp A -> hProp B -> hProp (A * B).
Proof.
  intros hA hB (a1,b1) (a2, b2).
  rewrite (hA a1 a2), (hB b1 b2).
  reflexivity.
Qed.

Lemma eq_true_hProp b : hProp (eq_true b).
Proof.
  case b; intros x y; destruct y;
  exact (match x in (eq_true true) return (x = is_eq_true) with
    is_eq_true => eq_refl
  end).
Qed.

Lemma eq_true_equal_true [b] : eq_true b -> b = true.
Proof.
  destruct b; auto. intros H. apply false_elim; trivial.
Qed.

Lemma orb_elim [a b : bool] : orb a b -> a \/ b.
Proof.
  destruct a; try (left; easy).
  destruct b; try (left; easy). right; easy.
Qed.

Lemma andb_elim [a b : bool] : andb a b -> a /\ b.
Proof.
  split; destruct a; easy.
Qed.

Lemma sigT_bool_eq T (B : T -> bool) : forall x y : {v:T & B v},
  projT1 x = projT1 y -> x = y.
Proof.
  intros (v1,b1) (v2,b2). simpl. intros H. revert b1 b2. rewrite H.
  intros b1 b2.
  rewrite (eq_true_hProp (B v2) b1 b2).
  reflexivity.
Qed.


Definition dec (T : Type) (b : bool) : Type := (T -> b) * (b -> T).

Lemma dec_true T : dec T true -> T.
Proof.
  intros (T_true,true_T); apply true_T; easy.
Qed.

Lemma dec_false T : dec T false -> T -> Empty_set.
Proof.
  intros (T_false, false_T). intros t. apply false_elim, T_false, t.
Qed.

Lemma dec_false_inv T : (T -> Empty_set) -> dec T false.
Proof.
  intros notT. split; easy.
Qed.

Require Import Relation_Definitions.

Generalizable All Variables.

Definition rel T := T -> T -> bool.

Class Equivalence {T} (R : rel T) : Type := {
  reflexivity : reflexive _ R
; symmetry : symmetric _ R
; transitivity : transitive _ R
}.

Class Projection {T} (R : rel T) (pi : T -> T) := {
  pi_spec : forall x, R x (pi x)
; pi_respects_equiv : forall x y, R x y -> pi x = pi y
; pi_respects_equiv_inv : forall x y, pi x = pi y -> R x y
}.

Lemma pi_idempotent {T} (R : rel T) (pi : T -> T) `{Projection _ R pi} :
  forall x, pi x = pi (pi x).
Proof.
  intros x. apply pi_respects_equiv, pi_spec.
Qed.

(* Definition is_projection {T} (R : rel T) (pi : T -> T) :=
  forall x y, R x y <-> pi x = pi y. *)

Class EqDec T : Type :=
{
  eq_dec : forall (x y : T), {b & dec (x = y) b}
}.

(* Definition eq_dec T := forall (x y : T), {b & dec (x = y) b}.*)

Definition equal {T} `{EqDec T} x y := projT1 (eq_dec x y). 

Lemma equal_spec {T} `{EqDec T} {x y: T} : equal x y -> x = y.
Proof.
  unfold equal, eq_dec.
  destruct H as [H]. destruct (H x y) as [b (d1,d2)]. simpl.
  assumption.
Qed.

Lemma equal_spec_inv {T} `{EqDec T} {x y : T} : x = y -> equal x y.
Proof.
  unfold equal, eq_dec.
  destruct H as [H]. destruct (H x y) as [b (d1,d2)]. simpl.
  assumption.
Qed.

#[export]
Instance pair_EqDec : forall (A B : Type) `{EqDec A} `{EqDec B}, EqDec (A * B).
Proof.
  intros A B (EdA) (EdB). split. intros (a1,b1) (a2,b2).
  destruct (EdA a1 a2) as [aref abool].
  destruct (EdB b1 b2) as [bref bbool].
  revert abool bbool.
  case aref; case bref; intros H1 H2.
  exists true; apply dec_true in H1, H2; rewrite H1, H2; easy.
  all: exists false;
  [> pose (Q := dec_false _ H2) | pose (Q := dec_false _ H1) | pose (Q := dec_false _ H1)];
  apply dec_false_inv; intros H3; inversion H3; easy.
Defined.

(* Context T {Dec: eq_dec T}. *)

Definition quotient T (R : rel T) (pi : T -> T)
  `{EqDec T} := { x : T & equal x (pi x) }.

Lemma quotient_spec {T} {R : rel T}
  `[EqDec T] `[Equivalence _ R] `[Projection _ R pi]
  : forall (a b : quotient T R pi), a = b <-> R (projT1 a) (projT1 b).
Proof.
  split.
  - destruct a; destruct b; simpl. intros aEb. inversion aEb.
    apply reflexivity.
  - destruct a as [a aH]; destruct b as [b bH]; simpl.
    intros aRb.
    assert (a = b).
    {
      rewrite (equal_spec aH).
      rewrite (equal_spec bH).
      apply pi_respects_equiv; assumption.
    }
    revert aH bH aRb.
    rewrite H2.
    intros aH bH _.
    assert (aH = bH). { apply eq_true_hProp. }
    rewrite H3.
    reflexivity.
Qed.

(* Check quotient_spec. *)

#[export]
Instance quotient_EqDec {T} {R : rel T} (pi : T->T)
  `{EqDec T} `{Equivalence _ R} `{Projection _ R pi}
  : EqDec (quotient T R pi).
Proof.
  Opaque quotient.
  split; intros x y.
  (* split; intros (x,r1) (y,r2). *)
  destruct (eq_dec (projT1 x) (projT1 y)) as [e E].
  destruct e.
  - exists true. apply dec_true in E.
    pose (E' := reflexivity (R:=R) (projT1 x)).
    setoid_rewrite E at 2 in E'.
    apply (proj2 (quotient_spec x y)) in E'. split; easy.
  - exists false. pose (dec_false (projT1 x = projT1 y) E).
    apply dec_false_inv; intro E1; rewrite E1 in e.
    apply e; reflexivity.
  Transparent quotient.
Defined.

(* Check quotient_EqDec. *)