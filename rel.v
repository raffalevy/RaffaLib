Check 3.

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Minus.



Set Implicit Arguments.

Section CongMod.

Parameter m : nat.

Definition cong_mod (a b : nat) : Prop :=
  exists k, a = b + k * m \/ a + k * m = b.

Lemma cong_mod_refl : reflexive _ cong_mod.
Proof.
  intros a. exists 0. left. rewrite <- plus_n_O. reflexivity.
Qed.

Lemma cong_mod_symm : symmetric _ cong_mod.
Proof.
  intros a b H. destruct H as [k [H | H]]; exists k.
  - right. rewrite H. reflexivity.
  - left. rewrite H. reflexivity.
Qed.

Axiom cong_mod_trans : transitive _ cong_mod.

(* Lemma cong_mod_trans : transitive _ cong_mod.
Proof.
  intros a b c H1 H2.
  destruct H1 as [k1 [H1|H1]];
  destruct H2 as [k2 [H2|H2]].
  - rewrite H2 in H1.
    rewrite <- Nat.add_assoc, <- Nat.mul_add_distr_r in H1.
    exists (k2 + k1).
    left. assumption.
  -  *)
  

    (* assert (E : k2 * m + k1 * m = (k2 + k1) * m).
    rewrite  Nat.mul_add_distr_r. *)


Add Parametric Relation : nat cong_mod
  reflexivity proved by cong_mod_refl
  symmetry proved by cong_mod_symm
  transitivity proved by cong_mod_trans
  as cong_mod_rel.

(* Check Nat.add. *)

Add Parametric Morphism : (Nat.add) with
  signature cong_mod ==> cong_mod ==> cong_mod as add_mor_cong_mod.
Proof.
  give_up.
Admitted.

Goal forall a b, cong_mod a b -> cong_mod ((a + b) + b) (3 * b).
Proof.
  intros a b H.
  rewrite H.
  simpl. rewrite <-plus_n_O, Nat.add_assoc.
  reflexivity.
Qed.

End CongMod.