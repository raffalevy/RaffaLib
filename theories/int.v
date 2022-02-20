Require Import Coq.Arith.PeanoNat.

From RaffaLib Require Import basic structures nat.

Section Int.

Local Fixpoint reduce_nat_pair' (a b : nat) :=
  match (a, b) with
  | (0, b) => (0, b)
  | (a, 0) => (a, 0)
  | (S a, S b) => reduce_nat_pair' a b
  end.

Definition reduce_nat_pair (ab : nat * nat) :=
  let (a,b) := ab in reduce_nat_pair' a b.

Definition int : Type := groth Nat.add reduce_nat_pair.

Local Lemma reduce_nat_pair_cancel : forall a b x,
  reduce_nat_pair' (x + a) (x + b) = reduce_nat_pair' a b.
Proof. induction x; auto. Qed.

Local Definition swap (ab : nat * nat) :=
  let (a,b) := ab in (b,a).

Local Lemma reduce_swap : forall ab : nat * nat, reduce_nat_pair (swap ab) = swap (reduce_nat_pair ab).
Proof.
  intros (a,b).
  apply (@nat_double_ind (fun a b => reduce_nat_pair (swap (a, b)) = swap (reduce_nat_pair (a, b))));
  simpl; try auto; destruct n; auto.
Qed.

Local Lemma reduce_minus : forall a b x : nat, reduce_nat_pair' a b = (x,0) -> x + b = a.
Proof.
  intros a b x.
  apply (@nat_double_ind (fun a b => reduce_nat_pair' a b = (x, 0) -> x + b = a));
  simpl; try (intros n; inversion 1; apply Nat.add_0_r).
  clear a b; intros a b. intros H1 H2. apply H1 in H2.
  rewrite <-plus_n_Sm, H2; reflexivity.
Qed.

Local Lemma reduce_reaches_zero : forall a b : nat,
  (exists x, reduce_nat_pair' a b = (x,0)) \/ (exists x, reduce_nat_pair' a b = (0,x)).
Proof.
  intros a b.
  apply (@nat_double_ind (fun a b => (exists x : nat, reduce_nat_pair' a b = (x, 0)) \/
  (exists x : nat, reduce_nat_pair' a b = (0, x)))); simpl;
  trivial; intros n; [> right; exists n | left; exists (S n)]; trivial.
Qed.

Local Lemma reduce_ge : forall a b c d x : nat,
  reduce_nat_pair' a b = reduce_nat_pair' c d -> reduce_nat_pair' a b = (x, 0)
  -> a + d = b + c.
Proof.
  intros a b c d x H H1.
  assert ( H2 : reduce_nat_pair' c d = (x,0) ) by (rewrite <-H; assumption);
  apply reduce_minus in H1, H2;
  rewrite <-H1, <-H2;
  rewrite Nat.add_assoc;
  setoid_rewrite Nat.add_comm at 2; reflexivity.
Qed.

Local Lemma swap_swap : forall xy, swap (swap xy) = xy.
Proof. destruct xy; trivial. Qed.

Local Lemma swap_reduce_eq : forall a b c d,
  reduce_nat_pair' a b = reduce_nat_pair' c d
  -> reduce_nat_pair' b a = reduce_nat_pair' d c.
Proof.
  intros a b c d H.
  assert (Q : forall a b, reduce_nat_pair' b a = swap (reduce_nat_pair' a b)) by (
    intros a' b';
    change (reduce_nat_pair' a' b') with (reduce_nat_pair (a',b'));
    rewrite <-reduce_swap; reflexivity
  ).
  rewrite (Q a b), (Q c d), H; trivial.
Qed.

#[export]
Instance reduce_nat_pair_Projection : Projection (ueq Nat.add) reduce_nat_pair.
Proof.
  split.
  - intros (a,b); simpl.
    apply (@nat_double_ind (fun a b => eq_true (let (c, d) := reduce_nat_pair' a b in equal (a + d) (b + c))));
    try (intros n; simpl; apply equal_spec_inv; rewrite Nat.add_0_r; reflexivity).
    clear a b; intros a b; simpl.
    destruct (reduce_nat_pair' a b) as [c d]; intros H.
    apply equal_spec_inv; apply equal_spec in H; auto.
  - intros (a,b) (c,d); simpl; intros H; apply equal_spec in H.
    rewrite <-(reduce_nat_pair_cancel a b c),
            <-(reduce_nat_pair_cancel c d a).
    setoid_rewrite Nat.add_comm at 1 2.
    rewrite H; trivial.
  - intros (a,b) (c,d); simpl; intros H; apply equal_spec_inv.
    destruct (reduce_reaches_zero a b) as [(x,H1)|(x,H1)].
    + exact (reduce_ge a b c d x H H1).
    + assert (Q : reduce_nat_pair' a b = reduce_nat_pair (swap (b,a))) by trivial.
      pose (Q1 := H1); rewrite Q, reduce_swap in Q1.
      assert (Q2 : swap (swap (reduce_nat_pair (b, a))) = swap (0, x)) by (rewrite Q1; trivial).
      rewrite swap_swap in Q2; simpl in Q2.
      pose (H' := swap_reduce_eq a b c d H).
      symmetry; exact (reduce_ge b a d c x H' Q2).
Qed.

Definition nat_to_int (n : nat) : int := to_groth Nat.add reduce_nat_pair n.

Coercion nat_to_int : nat >-> int.

End Int.