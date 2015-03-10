Require Import NArith.
Require Import Bool.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Open Scope nat_scope.

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
    rewrite eggT_equation. induction n. 
      simpl. reflexivity.
      rewrite Nat.mod_1_l.
        simpl. reflexivity.
        generalize n. simple induction n0. apply Nat.lt_1_2.
        intros. apply Lt.lt_S. exact H0.
Qed.
Hint Resolve ggT_n_1.

Theorem ggT_kom : forall n m : nat, eggT n m = eggT m n.
Proof.
  intros. pose ggT_0 as H1. induction m.
    apply H1. reflexivity. (*  induction m. simpl. rewrite ggT_n_1; reflexivity. *)
    rewrite eggT_equation. induction m. rewrite eggT_equation. 
    admit.
Qed.

Theorem ggT_impl : forall n m : nat, n >= m -> eggT n m = eggT (n - m) m.
Proof.
  intros n m H. induction m.
    rewrite <- Minus.minus_n_O. trivial.
    admit.
Qed.

Section Zahlentheorie.
Variables a b c r: nat.
Definition ggT : Set := nat -> nat -> nat.
Definition eggT : forall (n m : nat), gcd n m = gcd m n.
Proof. intros. unfold gcd.

Definition ggT (n m : nat) : Set :=  nat -> nat -> nat -> gcd 0 m = m /\ gcd n m = gcd m n.
Definition eggT_0 : forall m : nat, ggT 0 m.
Proof. intros. unfold gcd. intros. split. reflexivity. unfold NPeano.gcd. reflexivity. 


Definition eggT : forall (n m : nat), gcd n m = gcd m n.
Proof.  intros. unfold gcd.
Definition gcd_0 : gcd -> nat := forall n m : nat, n = 0 -> (gcd n m) -> m.
Inductive gcd (n m : nat) : Set := gcd_def : forall a : nat, n >= m -> a = n - m -> gcd n m.
(* Spezifikation vom ggT. Vom Typ Set. *)
(* Definition ggT (a b c : nat) := c. *)
(* Definition eggT : forall (a b: nat), {(ggT a b) = (ggT b a)} + {(ggT 0 b) -> b }.
Proof. intros. unfold ggT. auto.  *)
Definition ggT : Set := nat -> nat -> nat.
Fixpoint eggT ( a b : nat) :=
  match a with
    | 0 => b
    | S a => eggT(b mod a) (S a)
end.

Definition divide (a b : nat) : Type := { q | b = a * q }.
Definition gcd (a b : nat) : nat := prod
Definition is_gcd d a b :=  prod (divide d a)    (prod (divide d b)      (forall x, divide x a -> divide x b -> divide x d)).Lemma gcd_correct :  forall a b s, Z0 <= a -> Z0 <= b ->{d| prod (        [("gcd", ["a", "b"], gcd_body)]⊢⟨gcd_body |MEM"a"a::MEM"b"b::PROC::s⟩→* ⟨ return #d | MEM "a" a :: MEM "b" b :: PROC :: s ⟩      )      (is_gcd d a b) }.


Fixpoint eggT ( a b : nat) : Set :=
 if (a < b ) then
  match a with
    | 0 => b
    | S a => eggT(b mod a) (S a)
end
else eggT b a.
end. 

Definition ggT : forall a b : nat, (ggT a b) = (ggT b a).
Definition ggT : Set := nat -> nat -> nat.
Definition ggT_kom := forall a b : nat, (ggT a b) = (ggT b a).
(* Hypothesis kommutativ : ( forall f : ggT, f a b = f b a). *)

(* Definition eggT : ggT := fun a b=> if (Zeq_bool b 0) then a else 
  if (Zeq_bool (a mod b) 0 ) then b else 0. *)

(* Theorem kommutativ :  eggT a b = eggT b a. *)
End Zahlentheorie.
Eval compute in (5 mod 0).

Fixpoint eggT (a b : Z)  :=
 match a with
   | 0 => b
   | Zsucc a' => eggT (b mod a) (Zsucc a)
  end.

Fixpoint eggT (a b : Z)  :=
  match b with
   | 0 => a
   | _ => let m := (a mod b) in
       if (Zeq_bool m 0 ) then b else eggT b m 
  end.


Close Scope Z_scope.