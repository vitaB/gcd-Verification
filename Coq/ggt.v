Require Import NPeano.
Require Import Omega.

Open Scope nat_scope.

Lemma mod_t : forall n m k,  m > 0 -> (n + k * m) mod m = n mod m.
Proof.
  induction k; intro.
    simpl. rewrite Nat.add_0_r. trivial.
    rewrite <- IHk. symmetry. rewrite <- (Nat.mod_add _ 1).
    rewrite <- plus_assoc. rewrite <- Nat.mul_add_distr_r with(p:=m)(n:=k)(m:=1).
    rewrite Nat.add_1_r. trivial.
    omega. assumption.
Qed.

Lemma mod_diff : forall n m : nat, n>=m /\ m <> 0 -> (n - m) mod m = n mod m.
Proof. 
  intros n m [H1 H2]. 
  rewrite <- (Nat.mod_add _ 1). rewrite mult_1_l. rewrite Nat.sub_add. trivial.
   assumption.
   assumption.
Qed.

Function ggT ( a b : nat) : nat :=
match a with
   | 0 => b
   | S a' => ggT(b mod S a')  (S a')
end.

Theorem ggT_0 : forall m n : nat, m = 0 -> (ggT n m) = n.
Proof.
  intros. case_eq(n); intros.
    rewrite H. trivial.
    rewrite ggT_equation. rewrite H. rewrite Nat.mod_0_l by omega. trivial.
Qed.
Hint Resolve ggT_0.

Lemma ggT_n_1 : forall m n : nat, m = 1 -> (ggT n m) = 1.
Proof.
 intros. rewrite H. case_eq(n); intros.
  trivial.
  rewrite ggT_equation. case_eq(n0); intros.
    trivial.
    rewrite Nat.mod_1_l by omega. trivial.
Qed.
Hint Resolve ggT_n_1.

Lemma ggT_same : forall m n : nat, m = n -> ggT n m = n.
Proof.
  intros m n H; rewrite H. case_eq(n).
    reflexivity.
    intros. rewrite ggT_equation. rewrite Nat.mod_same by omega.
      trivial.
Qed.
Hint Resolve ggT_same.

Lemma ggt_mod : forall n m, m > 0 -> ggT n m = ggT (n mod m) m.
Proof.
  intros; case_eq(m); intros.
    (*start with 1 not with 0*)  
    exfalso; omega.
  assert ( H1 : n = S n0 \/ n < S n0 \/ n > S n0) by omega.
  destruct H1 as [H11 | [H12 | H13] ].
    rewrite H11. rewrite Nat.mod_same by omega; rewrite ggT_same by omega; reflexivity.
    rewrite Nat.mod_small; omega.
   case_eq(n); intros.
      exfalso; omega.
      rewrite ggT_equation. rewrite Nat.mod_small by omega. rewrite ggT_equation. trivial.
Qed.

Theorem ggT_kom : forall n m : nat, ggT n m = ggT m n.
Proof.
  intros; case_eq(m); intros.
    apply ggT_0. trivial.
    symmetry. rewrite ggT_equation. rewrite <- ggt_mod.
      trivial.
      apply gt_Sn_O.
Qed.

Theorem ggT_kom1 : forall n m : nat, ggT n m = ggT m n.
Proof.
  intros; pose ggT_0 as H1; induction m.
    apply H1; reflexivity.
    symmetry; rewrite ggT_equation. rewrite <- ggt_mod; trivial.
      generalize m. simple induction m0.
      apply Nat.lt_0_1.
      intros. apply Lt.lt_S. exact H.
Qed.

Theorem ggT_impl : forall n m : nat, n >= m -> ggT n m = ggT (n - m) m.
Proof.
  intros. case_eq(m).
    rewrite Nat.sub_0_r. trivial.
    intros.
    symmetry. rewrite ggT_kom. rewrite ggT_equation. rewrite mod_diff.
    symmetry. rewrite ggT_kom. rewrite ggT_equation.
      trivial.
      split.
        rewrite <- H0. exact H.
        apply(Nat.neq_succ_0).
Qed.
Close Scope Z_scope.