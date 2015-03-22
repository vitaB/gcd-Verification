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

(* ggT(n,m) = ggT(m, n)
ggT(0,n) = n
n >= m -> ggT(n, m) = ggT(n - m, n)
 *)

Function eggT ( a b : nat) : nat :=
match a with
   | 0 => b
   | S a' => eggT(b mod S a')  (S a')
end.

Theorem ggT_0 : forall m n : nat, m = 0 -> (eggT n m) = n.
Proof.
 intros m n H; rewrite H. induction n. 
  simpl. reflexivity.
  simpl. rewrite Minus.minus_diag. simpl. reflexivity.
Qed.
Hint Resolve ggT_0.
Lemma ggT_n_1 : forall m n : nat, m = 1 -> (eggT n m) = 1.
Proof. 
  intros m n H; rewrite H; induction n.
    simpl. reflexivity.
    rewrite eggT_equation. case n. 
      simpl; reflexivity.
      intros. rewrite Nat.mod_1_l.
        simpl; reflexivity.
        generalize n0. simple induction n1. apply Nat.lt_1_2.
        intros. apply Lt.lt_S. exact H0.
Qed.
Hint Resolve ggT_n_1.

Lemma ggT_same : forall m n : nat, m = n -> eggT n m = n.
Proof.
  intros m n H; rewrite H. induction n.
    reflexivity.
     rewrite eggT_equation. rewrite Nat.mod_same.
        reflexivity. pose Nat.neq_succ_0. apply n0.
Qed.
Hint Resolve ggT_same.

Lemma ggt_mod : forall n m, m > 0 -> eggT n m = eggT (n mod m) m.
Proof. 
  induction m; intro.
    (*start with 1 not with 0*)  
    exfalso; omega.
  assert ( n = S m \/ n < S m \/ n > S m) by omega.
  destruct H0 as [H01 | [H02 | H03] ].
    rewrite H01; rewrite Nat.mod_same by omega; rewrite ggT_same by omega; reflexivity.
    rewrite Nat.mod_small; omega.
    destruct n.
      exfalso; omega.
      rewrite eggT_equation. rewrite Nat.mod_small by omega. rewrite eggT_equation. trivial.
Qed.

Theorem ggT_kom : forall n m : nat, eggT n m = eggT m n.
Proof.
  intros. induction m. simpl. apply ggT_0. trivial.
    rewrite eggT_equation. rewrite eggT_equation. rewrite <- eggT_equation.
      apply ggt_mod. apply gt_Sn_O. SearchAbout( S _ > 0).
Qed.

Theorem ggT_kom1 : forall n m : nat, eggT n m = eggT m n.
Proof.
  intros; pose ggT_0 as H1; induction m.
    apply H1; reflexivity.
    symmetry; rewrite eggT_equation. rewrite <- ggt_mod; trivial.
      generalize m. simple induction m0.
      apply Nat.lt_0_1.
      intros. apply Lt.lt_S. exact H.
Qed.

Theorem ggT_impl : forall n m : nat, n >= m -> eggT n m = eggT (n - m) m.
Proof.
  intros. induction m.
    rewrite Nat.sub_0_r; trivial.
    rewrite ggT_kom. rewrite eggT_equation.
    symmetry. rewrite ggT_kom. rewrite eggT_equation. rewrite mod_diff.
    trivial. omega. 
Qed.
Close Scope Z_scope.