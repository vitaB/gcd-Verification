Require Import ZArith.
Require Import ZArith.BinInt.
Require Import Bool.
Open Scope Z_scope.


Section Zahlentheorie.
Variables a b c r: Z.
(* Spezifikation vom ggT. Vom Typ Set. *)
Definition ggT : Set := Z -> Z -> Z.
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