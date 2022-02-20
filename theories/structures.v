From RaffaLib Require Import basic.

Require Import Setoid.

Declare Scope structure_scope.
Delimit Scope structure_scope with structure_scope.

Section Structures.

Open Scope structure_scope.

Context {T : Type}.

(* Class TypeWithBinop : Type := {
  op : T -> T -> T
}. *)

Definition binop := T -> T -> T.

Context (op : binop).

Notation "x * y" := (op x y) : structure_scope.

(* Context `{TypeWithBinop}. *)

Class Monoid : Type := {
  id : T
; associativity : forall (x y z : T), x * (y * z) = x * y * z
; left_identity : forall x : T, id * x = x
; right_identity : forall x : T, x * id = x
}.

Class Commutative : Type :=
  commutativity : forall x y : T, x * y = y * x.

Class LeftCancellative : Type :=
  left_cancellativity : forall a b x : T, x * a = x * b -> a = b.

Class Group : Type := {
  Group_Monoid :> Monoid
; inv : T -> T
; left_inverse : forall x : T, inv x * x = id
; right_inverse : forall x : T, x * inv x = id
}.


Close Scope structure_scope.

End Structures.


Section Grothendieck.

Declare Scope groth_scope.
Delimit Scope groth_scope with groth_scope.
Open Scope groth_scope.

Context {T : Type}.

Context (op : binop (T:=T)).

Context `{Monoid T op} `{Commutative T op} `{LeftCancellative T op} `{EqDec T}.

Notation "x + y" := (op x y) : groth_scope.

Definition U : Type := T * T.

Definition ueq : rel U := fun ab cd =>
  let (a,b) := ab in let (c,d) := cd in
  equal (a + d) (b + c).

Notation "x == y" := (ueq x y) (at level 70, no associativity) : groth_scope.

#[local]
Instance ueq_Equivalence : Equivalence ueq.
Proof.
  split.
  - intros (a,b). simpl. rewrite commutativity by assumption.
    apply equal_spec_inv. reflexivity.
  - intros (a,b) (c,d). simpl.
    intros H3.
    apply equal_spec_inv; apply equal_spec in H3.
    setoid_rewrite commutativity at 1 2; try assumption.
    rewrite H3. reflexivity.
  - intros (a,b) (c,d) (e,f). simpl.
    intros H3 H4; apply equal_spec_inv; apply equal_spec in H3,H4.
    apply (left_cancellativity op _ _ (c + d)).
    assert (Q1: c + d + (a + f) = (a + d) + (c + f)). {
      setoid_rewrite associativity at 1 2; try assumption.
      setoid_rewrite commutativity at 2; try assumption.
      setoid_rewrite commutativity at 3; try assumption.
      setoid_rewrite associativity at 1; try assumption.
      reflexivity.
    }
    assert (Q2 : c + d + (b + e) = (b + c) + (d + e)). {
      setoid_rewrite associativity at 1 2; try assumption.
      setoid_rewrite commutativity at 2; try assumption.
      setoid_rewrite associativity at 1; try assumption.
      reflexivity.
    }
    rewrite Q1, Q2, H3, H4.
    reflexivity.
Qed.

Context (pi : U -> U) `{Projection _ ueq pi}.

Definition groth := quotient U ueq pi.

(* Lemma pi_idempotent : forall x, pi (pi x) = pi x.
Proof.
  (* x ==  *)
  intros x.
  (* assert (pi (pi x) == pi x). *)
  apply pi_respects_equiv. apply *)

Let addU (x y : U) : U :=
  let (a,b) := x in let (c,d) := y in (a+c, b+d).

Let groth_op_val (x y : groth) : U :=
  pi (addU (projT1 x) (projT1 y)).

Let groth_op_spec (x y : groth) : equal (groth_op_val x y) (pi (groth_op_val x y)).
Proof.
  apply equal_spec_inv.
  unfold groth_op_val.
  apply (pi_idempotent ueq); assumption.
Qed.

Definition groth_op (x y : groth) : groth :=
  existT _ (groth_op_val x y) (groth_op_spec x y).

Notation "x +' y" := (groth_op x y) (at level 50, left associativity) : groth_scope.

Lemma addU_respects : forall x1 y1 x2 y2 : U,
  x1 == x2 -> y1 == y2 -> addU x1 y1 == addU x2 y2.
Proof.
  intros (a1,b1) (c1,d1) (a2,b2) (c2,d2).
  unfold ueq; simpl.
  intros EX EY.
  apply equal_spec in EX, EY; apply equal_spec_inv.

  setoid_rewrite associativity; try assumption.
  setoid_rewrite <-associativity at 2 4; try assumption.
  setoid_rewrite commutativity at 3 6; try assumption.
  setoid_rewrite associativity; try assumption.
  setoid_rewrite <-associativity; try assumption.
  rewrite EX, EY; reflexivity.
Qed.

Definition pi_groth (x:U) : groth.
Proof.
  exists (pi x).
  apply equal_spec_inv.
  rewrite <-(pi_idempotent ueq); trivial.
Defined.

Definition to_groth (x:T) : groth := pi_groth (x, id op).

(* Definition to_groth (x:T) : groth.
Proof.
  exists (pi (x, id op)).
  apply equal_spec_inv.
  rewrite <-(pi_idempotent ueq); trivial.
Defined. *)

#[export]
Instance groth_Commutative : Commutative groth_op.
Proof.
  intros ((a,b),r1) ((c,d),r2); simpl.
  apply sigT_bool_eq; simpl; unfold groth_op_val; apply pi_respects_equiv.
  simpl; apply equal_spec_inv.
  setoid_rewrite commutativity at 1.
  setoid_rewrite commutativity at 2 3.
  reflexivity. all: assumption.
Qed.

Lemma groth_left_identity : forall x : groth, to_groth (id op) +' x = x.
Proof.
  intros ((a,b),r).
  apply sigT_bool_eq; simpl.
  setoid_rewrite (equal_spec r) at 2.
  unfold groth_op_val; apply pi_respects_equiv; simpl.
  assert (Q1 : (a,b) = addU (id op, id op) (a,b)). {
    simpl. rewrite 2left_identity. reflexivity.
  }
  setoid_rewrite Q1 at 2.
  apply addU_respects.
  + apply (symmetry (R:=ueq)), pi_spec.
  + apply (reflexivity (R:=ueq)).
Qed.

#[export]
Instance groth_Monoid : Monoid groth_op.
Proof.
  exists (to_groth (id op)).
  - intros ((a1,b1),r1) ((a2,b2),r2) ((a3,b3),r3).
    enough (Q : addU (a1,b1) (pi (addU (a2,b2) (a3,b3))) == addU (pi (addU (a1,b1) (a2,b2))) (a3,b3)). {
      apply sigT_bool_eq. simpl.
      unfold groth_op_val. apply pi_respects_equiv.
      Opaque addU.
      unfold groth_op_val; simpl; unfold groth_op_val; simpl.
      assumption.
    }
    enough (Q1 : addU (a1,b1) (addU (a2,b2) (a3,b3)) = addU (addU (a1,b1) (a2,b2)) (a3,b3)). {
      enough (Q2 : addU (a1, b1) (addU (a2, b2) (a3, b3)) == addU (a1, b1) (pi (addU (a2, b2) (a3, b3)))).
      enough (Q3 : addU (addU (a1, b1) (a2, b2)) (a3, b3) == addU (pi (addU (a1, b1) (a2, b2))) (a3, b3)).
      2,3: apply addU_respects; try apply pi_spec; try apply (reflexivity (R:=ueq)).
      apply (symmetry (R:=ueq)) in Q2.
      rewrite Q1 in Q2.
      apply (transitivity (R:=ueq) Q2 Q3).
    }
    Transparent addU. simpl.
    setoid_rewrite associativity; try assumption. reflexivity.
  - apply groth_left_identity. 
  - intros x. rewrite commutativity.
    + apply groth_left_identity. + apply groth_Commutative.
Defined.

Let neg (x : groth) := let (a,b) := projT1 x in pi_groth (b,a).

Local Lemma groth_left_inverse : forall x : groth, neg x +' x = id groth_op.
Proof.
  intros ((a,b),r). unfold neg; simpl.
  apply sigT_bool_eq; simpl; unfold groth_op_val; simpl.
  apply pi_respects_equiv.
  assert (Q: addU (b,a) (a,b) == addU (pi (b, a)) (a, b)). {
    apply addU_respects; try apply pi_spec; try apply (reflexivity (R:=ueq)).
  }
  apply (symmetry (R:=ueq)) in Q; apply (transitivity (R:=ueq) Q).
  simpl; apply equal_spec_inv.
  setoid_rewrite commutativity at 2; try assumption.
  reflexivity.
Qed.


#[export]
Instance groth_Group : Group groth_op.
Proof.
  exists groth_Monoid neg.
  - apply groth_left_inverse.
  - intros x. rewrite commutativity.
    + apply groth_left_inverse. + apply groth_Commutative.
Qed.

Close Scope groth_scope.
End Grothendieck.

Check groth.