Require Import human_readable.
Require Import Coq.Classes.RelationClasses.
Require Import Omega.

Fixpoint ack (x y : nat) : nat :=
  match x with
  | 0 => S y
  | S x' => let fix ackn (y : nat) :=
               match y with
               | 0 => ack x' 1
               | S y' => ack x' (ackn y')
               end
           in ackn y
  end.

Proposition ack_def0 :
  forall y : nat, ack 0 y = S y.
Proof.
  intros y.
  simpl.
  reflexivity.
Qed.

Proposition ack_def1 :
  forall x : nat, ack (S x) 0 = ack x 1.
Proof.
  intros x.
  simpl.
  reflexivity.
Qed.

Proposition ack_def2 :
  forall x y : nat, ack (S x) (S y) = ack x (ack (S x) y).
Proof.
  intros x y.
  simpl.
  reflexivity.
Qed.

Lemma ack_1_y :
  forall y : nat , ack 1 y = y + 2.
Proof.
  intros y.
  induction y.
  - Left
    = (ack 1 0).
    = 2.
    = Right.
  - Left
    = (ack 1 (S y)). 
    = (ack 0 (ack 1 y))  { by ack_def2 }.
    = (S (ack 1 y))      { by ack_def0 }.
    = (S (y + 2))        { by IHy }.
    = (S y + 2).
    = Right.
Qed.

Instance refge : (Reflexive ge).
Proof.
  unfold Reflexive.
  intros x.
  omega.
Qed.

Instance trage : (Transitive ge).
Proof.
  unfold Transitive.
  intros x y z.
  omega.
Qed.

Lemma ack_Sx_y_ge_SSy :
  forall x y : nat , ack (S x) y >= S (S y).
Proof.
  intros x.
  induction x.
  - intros y.
    Left
    = (ack 1 y).
    = (y + 2)    {by ack_1_y}.
    = (S (S y))  {omega}.
    = Right.
  - intros y.
    induction y.
    + Left
      = (ack (S (S x)) 0).
      = (ack (S x) 1).
      <ge>* 3  {apply IHx}.
      <ge>* 2  {omega}.
      = Right.
    + Left
      = (ack (S x) (ack (S (S x)) y)).
      <ge>* (S(S(ack (S (S x)) y)))  { apply IHx }.
      <ge>* (S(S(S(S y))))
         { assert (forall x y : nat,
                      x >= y -> (S (S x)) >= (S (S y)))
           as H by (intros H0 H1 ; omega) ;
           apply (H (ack (S (S x)) y) (S (S y)) IHy)
         }.
      <ge>* (S(S(S y)))   { omega }.
      = Right.
Qed.


Lemma ack_x_y_ge_Sy :
  forall x y : nat , ack x y >= S y.
Proof.
  intros x.
  induction x.
  - intros y.
    Left
    = (ack 0 y).
    = (S y).
    = Right.
  - intros y.
    Left
    = (ack (S x) y).
    <ge>* (S (S y)) { apply ack_Sx_y_ge_SSy }.
    <ge>* (S y)     { omega }.
    = Right.
Qed.

Lemma ack_x_y_gt_Sy :
  forall x y : nat , ack x y > y.
Proof.
  intros x y.
  assert (forall x y : nat , x >= S y -> x > y) as H by (intros x0 y0 ; omega).
  apply H.
  apply ack_x_y_ge_Sy.
Qed.

Lemma ack_x_y_lt_ack_x_Sy :
  forall x y : nat , ack x y < ack x (S y).
Proof.
  intros x.
  induction x.
  - intros y.
    Left
    = (S y).
    <lt> (S (S y))   { omega }.
    = Right.
  - intros y.
    Left
    = (ack (S x) y).
    <le> (ack x (ack (S x) y))   {apply ack_x_y_gt_Sy}.
    = (ack (S x) (S y)).
    = Right.
Qed.

Lemma ack_y_mono_increasing :
  forall x y y' : nat , y <= y' -> ack x y <= ack x y'.
Proof.
  intros x y y' H.
  induction H.
  - reflexivity.
  - Left
    = (ack x y).
    <lt>* (ack x m)     { apply IHle }.
    <lt>* (ack x (S m)) { apply (Nat.lt_le_incl
                                   (ack x m)
                                   (ack x (S m))
                                   (ack_x_y_lt_ack_x_Sy x m)) }.
    = Right.
Qed.
  
Lemma ack_x_Sy_le_ack_Sx_y :
  forall x y : nat , ack x (S y) <= ack (S x) y.
Proof.
  intros x y.
  induction y.
  - Left
    = (ack x 1).
    = (ack (S x) 0).
    = Right.
  - Left
    = (ack x (S (S y))).
    <lt>* (ack x (ack (S x) y))  { apply (ack_y_mono_increasing
                                     x
                                     (S (S y))
                                     (ack (S x) y)
                                     (ack_Sx_y_ge_SSy x y))
                                 }.
    = (ack (S x) (S y)).
    = Right.
Qed.


Lemma ack_x_y_le_ack_Sx_y :
  forall x y : nat , ack x y <= ack (S x) y.
Proof.
  intros x y.
  Left
  = (ack x y).
  <lt>* (ack x (S y))   { apply (Nat.lt_le_incl
                                   (ack x y)
                                   (ack x (S y))
                                   (ack_x_y_lt_ack_x_Sy x y))
                        }.
  <lt>* (ack (S x) y)   { apply ack_x_Sy_le_ack_Sx_y }.
  = Right.
Qed.

Lemma ack_x_mono_increasing :
  forall x x' y : nat , x <= x' -> ack x y <= ack x' y.
Proof.
  intros x x' y H.
  induction H.
  - reflexivity.
  - Left
    = (ack x y).
    <lt>* (ack m y)     { apply IHle }.
    <lt>* (ack (S m) y) { apply ack_x_y_le_ack_Sx_y  }.
    = Right.
Qed.

Lemma ack_inc :
  forall c1 c2 : nat , exists c3 : nat , forall x : nat ,
        ack c1 (ack c2 x) <= ack c3 x.
Proof.
  intros c1 c2.
  remember (max c1 c2) as c3.
  exists (S (S c3)).
  assert (c1 <= c3) as H0.
  - Left
    = c1.
    <le>* (max c1 c2) { apply Nat.le_max_l }.
    = c3              { by Heqc3 }.
    = Right.
  - assert (c2 <= S c3) as H1.
    + Left
      = c2.
      <le>* (max c1 c2)   { apply Nat.le_max_r }.
      = c3                { by Heqc3 }.
      <le>* (S c3)        { omega }.
      = Right.
    + intros x.
      Left
      = (ack c1 (ack c2 x)).
      <lt>* (ack c3 (ack c2 x))      { apply ack_x_mono_increasing ; apply H0 }.
      <lt>* (ack c3 (ack (S c3) x))  { apply ack_y_mono_increasing ; apply ack_x_mono_increasing ; apply H1 }.
      = (ack (S c3) (S x)).
      <lt>* (ack (S (S c3)) x)       { apply ack_x_Sy_le_ack_Sx_y }.
      = Right.
Qed.
