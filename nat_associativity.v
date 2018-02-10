Require Import human_readable.

Inductive Nat : Type :=
  Z : Nat
| S : Nat -> Nat.

Fixpoint plus (n : Nat) (m : Nat) : Nat :=
  match n with
  | Z => m
  | S n' => S(plus n' m)
  end.

Notation "x ＋ y" := (plus x y) (at level 50, no associativity).

Proposition plus_assoc :
  forall x y z : Nat , (x ＋ y) ＋ z = x ＋ (y ＋ z).
Proof.
  intros x y z.
  induction x.
  - Left
    = ((Z ＋ y) ＋ z).
    = (y ＋ z).
    = (Z ＋ (y ＋ z)).
    = Right.
  - Left
    = ((S x ＋ y) ＋ z).
    = (S (x ＋ y) ＋ z).
    = (S ((x ＋ y) ＋ z)).
    = (S (x ＋ (y ＋ z)))  {by IHx}.
    = ((S x) ＋ (y ＋ z)).
    = Right.
Qed.
