From RaffaLib Require Import basic structures.

From Coq.Arith Require Import PeanoNat Plus.

#[export]
Instance nat_add_Monoid : Monoid Nat.add := {
  id := 0
; associativity := Nat.add_assoc
; left_identity := Nat.add_0_l
; right_identity := Nat.add_0_r
}.

#[export]
Instance nat_add_LeftCancellative : LeftCancellative Nat.add := {
  left_cancellativity := plus_reg_l
}.

#[export]
Instance nat_add_Commutative : Commutative Nat.add := {
  commutativity := Nat.add_comm
}.

#[export]
Instance nat_EqDec : EqDec nat.
Proof.
  split; intros x y; case (Nat.eq_dec x y);
  intros H; [> exists true | exists false]; split; easy.
Defined.