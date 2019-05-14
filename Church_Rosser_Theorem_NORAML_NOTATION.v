Require Import Arith.
Require Import Omega.
Require Import String.
Require Import Coq.Relations.Relation_Definitions.

Lemma excluded_middle_b :
  forall b : bool , (b = true) \/ (b = false).
Proof.
  intros b.
  induction b.
  - left.
    reflexivity.
  - right.
    reflexivity.
Qed.

Tactic Notation "ifcase" uconstr(i) :=
  try case (excluded_middle_b i)
  ; [
    let H := fresh "Ht" in (
      intros H ;
      try rewrite H
    )
  |
  let H := fresh "Hf" in (
    intros H ;
    try rewrite H
  )
  ].


Module Term_shift_substitution.
  
  Inductive Term :=
    Var : nat -> Term
  | App : Term -> Term -> Term
  | Abs : Term -> Term
  .

  Fixpoint shift (c : nat) (d : nat) (M : Term) : Term :=
    match M with
    | (Var x)     => if (x <? c) then (Var x) else (Var (x + d)) 
    | (App M1 M2) => App (shift c d M1) (shift c d M2)
    | (Abs M1)    => Abs (shift (S c) d M1)
    end.

  Fixpoint substitution (M : Term) (x : nat) (N : Term) : Term :=
    match M with
    | (Var y)     => if (x <? y) then (Var (pred y)) else (if (x =? y) then N else M)
    | (App M1 M2) => App (substitution M1 x N) (substitution M2 x N)
    | (Abs M')    => Abs (substitution M' (S x) (shift 0 1 N))
    end.

  Notation "M [ x := N ]" := (substitution M x N) (at level 5, no associativity).

End Term_shift_substitution.
  
Section Shift_lemmas.

  Import Term_shift_substitution.
  
  Proposition shift_lemma00 :
    forall (M L : Term) , forall x : nat,
        (Abs M) [x := L] = Abs M [S x := shift 0 1 L].
  Proof.
    intros M.
    induction M.
    - intros L x.
      simpl.
      congruence.
    - intros L x.
      simpl.
      reflexivity.
    - intros L x.
      simpl.
      reflexivity.
  Qed.

  Lemma shift_lemma01 :
    forall M : Term, forall x y : nat,
        x <= y -> shift (S y) 1 (shift x 1 M) = shift x 1 (shift y 1 M).
  Proof.
    intros M.
    induction M.
    - intros x y H.
      simpl.
      ifcase (n <? x).
      * simpl.
        rewrite Nat.ltb_lt in Ht.
        assert (n <? S y = true).
        -- rewrite Nat.ltb_lt.
           induction H.
           ++ omega.
           ++ omega.
        -- rewrite H0.
           assert ( n <? y = true ).
           ++ rewrite Nat.ltb_lt.
              induction H.
              ** omega.
              ** omega.
           ++ rewrite H1.
              simpl.
              rewrite <- Nat.ltb_lt in Ht.
              rewrite Ht.
              reflexivity.
      * simpl.
        ifcase (n + 1 <? S y).
        -- rewrite Nat.ltb_lt in Ht.
           assert (n < y) by omega.
           rewrite <- Nat.ltb_lt in H0.
           rewrite H0.
           simpl.
           rewrite Hf.
           reflexivity.
        -- simpl.        
      + simpl.
        rewrite Nat.ltb_nlt in Hf0.
        assert (~ (n < y)) by omega.
        rewrite <- Nat.ltb_nlt in H0.
        rewrite H0.
        simpl.
        rewrite Nat.ltb_nlt in Hf.
        assert (~ (n + 1 < x)) by omega.
        rewrite <- Nat.ltb_nlt in H1.
        rewrite H1.
        reflexivity.
    - intros x y H.
      simpl.
      rewrite IHM1.
      + rewrite IHM2.
        * reflexivity.
        * exact H.
      + exact H.
    - intros x y H.
      simpl.
      rewrite IHM.
      * reflexivity.
      * induction H.
        -- reflexivity.
        -- omega.
  Qed.

  Proposition shift_lemma02 :
    forall M N : Term , forall x c : nat, 
        x <= c -> shift c 1 (M [x := N]) = (shift (S c) 1 M) [x := shift c 1 N].
  Proof.
    intros M.
    induction M.
    - intros N x c H.
      simpl.
      ifcase (x <? n).
      + rewrite Nat.ltb_lt in Ht.
        ifcase (n <? c).
        * rewrite Nat.ltb_lt in Ht0.
          assert (n < S c) by omega.
          assert (Init.Nat.pred n < c) by omega.
          rewrite <- Nat.ltb_lt in H0.
          rewrite <- Nat.ltb_lt in H1.
          simpl.
          rewrite H0.
          rewrite H1.
          induction n.
          -- simpl.
             assert (~ (x = 0)) as H2 by omega.           
             rewrite <- Nat.eqb_neq in H2.
             rewrite H2.
             reflexivity.
          -- simpl.
             rewrite <- Nat.ltb_lt in Ht.
             rewrite Ht.
             reflexivity.
        * rewrite Nat.ltb_nlt in Hf.
          ifcase (n <? S c).
          -- simpl.
             rewrite Nat.ltb_lt in Ht0.
             assert ( Init.Nat.pred n < c ) as H1 by omega.
             rewrite <- Nat.ltb_lt in H1.
             rewrite H1.
             rewrite <- Nat.ltb_lt in Ht.
             rewrite Ht.
             reflexivity.
          -- simpl.
             rewrite Nat.ltb_nlt in Hf0.
             assert ( ~ Init.Nat.pred n < c ) as H1 by omega.
             rewrite <- Nat.ltb_nlt in H1.
             rewrite H1.
             assert (x < n + 1) as H2 by omega.
             rewrite <- Nat.ltb_lt in H2.
             rewrite H2.
             assert ( Init.Nat.pred n + 1 = Init.Nat.pred (n + 1) ) as tmp by omega.
             rewrite tmp.
             reflexivity.
      + simpl.
        rewrite Nat.ltb_nlt in Hf.
        ifcase (n <? c).
        * rewrite Nat.ltb_lt in Ht.
          assert (n < S c) as H1 by omega.
          rewrite <- Nat.ltb_lt in H1.
          rewrite H1.
          simpl.
          rewrite <- Nat.ltb_nlt in Hf.
          rewrite Hf.
          rewrite Nat.ltb_nlt in Hf.
          rewrite Nat.ltb_lt in H1.
          ifcase (x =? n).
          -- reflexivity.
          -- simpl.
             rewrite <- Nat.ltb_lt in Ht.
             rewrite Ht.
             reflexivity.
        * rewrite Nat.ltb_nlt in Hf0.
          assert (n < S c) as H1 by omega.
          assert (x = n) as H2 by omega.
          rewrite <- Nat.eqb_eq in H2.
          rewrite <- Nat.ltb_lt in H1.
          rewrite H1, H2.
          simpl.
          rewrite <- Nat.ltb_nlt in Hf.
          rewrite Hf.
          rewrite H2.
          reflexivity.
    - intros N x c H.
      simpl.
      rewrite IHM1.
      + rewrite IHM2.
        * reflexivity.
        * exact H.
      + exact H.
    - intros N x c H.
      simpl.
      rewrite IHM.
      + rewrite shift_lemma01.
        * reflexivity.
        * omega.
      + omega.
  Qed.

  Lemma shift_lemma03 :
    forall M N : Term , forall c x : nat,
        c <= x -> shift c 1 (M [x := N]) = (shift c 1 M) [S x := shift c 1 N].
  Proof.
    induction M.
    - intros N c x H.
      simpl.
      ifcase (x <? n).
      + simpl.
        rewrite Nat.ltb_lt in Ht.
        assert (~ n < c) as H0 by omega.
        assert (~ Init.Nat.pred n < c) as H1 by omega.
        rewrite <- Nat.ltb_nlt in H0.
        rewrite <- Nat.ltb_nlt in H1.
        rewrite H0 , H1.
        simpl.
        assert (S x < n + 1) as H2 by omega.
        rewrite <- Nat.ltb_lt in H2.
        rewrite H2.
        assert (Init.Nat.pred n + 1 = Init.Nat.pred (n + 1)) as H3 by omega.
        rewrite H3.
        reflexivity.
      + ifcase (x =? n).
        * rewrite Nat.eqb_eq in Ht.
          rewrite Nat.ltb_nlt in Hf.
          assert (~ n < c) as H0 by omega.
          rewrite <- Nat.ltb_nlt in H0.
          rewrite H0.
          simpl.
          rewrite Nat.ltb_nlt in H0.
          assert (~ S x < n + 1) as H1 by omega.
          rewrite <- Nat.ltb_nlt in H1.
          rewrite H1.
          replace (n + 1) with (S n) by omega.
          rewrite <- Nat.eqb_eq in Ht.
          rewrite Ht.
          reflexivity.
        * rewrite Nat.eqb_neq in Hf0.
          rewrite Nat.ltb_nlt in Hf.
          ifcase (n <? c).
          -- simpl.
             rewrite Ht.
             rewrite Nat.ltb_lt in Ht.
             assert (~ S x < n) as H0 by omega.
             rewrite <- Nat.ltb_nlt in H0.
             rewrite H0.
             induction n.
             ++ reflexivity.
             ++ rewrite Nat.ltb_nlt in H0.
                assert (~ x = n) as H1 by omega.
                rewrite <- Nat.eqb_neq in H1.
                rewrite H1.
                reflexivity.
          -- simpl.
             rewrite Hf1.
             rewrite Nat.ltb_nlt in Hf1.
             assert (~ S x < n + 1) as H1 by omega.
             rewrite <- Nat.ltb_nlt in H1.
             rewrite H1.
             replace (n + 1) with (S n) by omega.
             rewrite <- Nat.eqb_neq in Hf0.
             rewrite Hf0.
             reflexivity.
    - intros N c x H.
      simpl.
      rewrite IHM1 , IHM2.
      + reflexivity.
      + exact H.
      + exact H.
    - intros N c x H.
      simpl.
      rewrite IHM.
      + rewrite shift_lemma01.
        reflexivity.
        omega.
      + omega.
  Qed.

  Lemma shift_lemma04 :
    forall (M N : Term) (x : nat) , (shift x 1 M) [x := N] = M.
  Proof.
    intros M.
    induction M.
    - intros M x.
      simpl.
      ifcase (n <? x).
      + simpl.
        rewrite Nat.ltb_lt in Ht.
        assert (~ x < n) as H0 by omega.
        rewrite <- Nat.ltb_nlt in H0.
        rewrite H0.
        assert (~ x = n) as H1 by omega.
        rewrite <- Nat.eqb_neq in H1.
        rewrite H1.
        reflexivity.
      + simpl.
        rewrite Nat.ltb_nlt in Hf.
        assert (x < n + 1) as H0 by omega.
        rewrite <- Nat.ltb_lt in H0.
        rewrite H0.
        replace (Init.Nat.pred (n + 1)) with n by omega.
        reflexivity.
    - intros N x.
      simpl.
      rewrite IHM1 , IHM2.
      reflexivity.
    - intros N x.
      simpl.
      rewrite IHM.
      reflexivity.
  Qed.

  Lemma shift_lemma05 :
    forall (M N L : Term) (x y : nat) ,
      x <= y
      -> (M [S y := shift x 1 L]) [x := N [y := L]] = (M [x := N]) [y := L].
  Proof.
    induction M.
    - intros N L x y H.
      simpl.
      ifcase (S y <? n).
      + simpl.
        rewrite Nat.ltb_lt in Ht.
        assert (x < Init.Nat.pred n) as H0 by omega.
        rewrite <- Nat.ltb_lt in H0.
        rewrite H0.
        assert (x < n) as H1 by omega.
        rewrite <- Nat.ltb_lt in H1.
        rewrite H1.
        simpl.
        rewrite Nat.ltb_lt in H0.
        rewrite Nat.ltb_lt in H1.
        assert (~ y = Init.Nat.pred n) as H2 by omega.
        rewrite <- Nat.eqb_neq in H2.
        rewrite H2.
        assert (y < Init.Nat.pred n) as H3 by omega.
        rewrite <- Nat.ltb_lt in H3.
        rewrite H3.
        reflexivity.
      + induction n.
        * simpl.
          ifcase (x =? 0).
          -- reflexivity.
          -- simpl.
             rewrite Nat.ltb_nlt in Hf.
             rewrite Nat.eqb_neq in Hf0.
             assert (~ y = 0) by omega.
             rewrite <-  Nat.eqb_neq in H0.
             rewrite H0.
             reflexivity.
        * ifcase (y =? n).
          -- rewrite Nat.ltb_nlt in Hf.
             rewrite Nat.eqb_eq in Ht.
             assert (x < S n) as H0 by omega.
             rewrite <- Nat.ltb_lt in H0.
             rewrite H0.
             simpl.
             rewrite Nat.ltb_lt in H0.
             assert (~ y < n) as H1 by omega.
             rewrite <- Nat.ltb_nlt in H1.
             rewrite H1.
             rewrite <- Nat.eqb_eq in Ht.
             rewrite Ht.
             simpl.
             rewrite shift_lemma04.
             reflexivity.
          -- simpl.
             ifcase (x <? S n).
             ++ simpl.
                rewrite Nat.ltb_nlt in Hf.
                rewrite Nat.eqb_neq in Hf0.
                rewrite Nat.ltb_lt in Ht.
                assert (~ y < n) as H0 by omega.
                rewrite <- Nat.ltb_nlt in H0.
                rewrite H0.
                assert (~ y = n) as H1 by omega.
                rewrite <- Nat.eqb_neq in H1.
                rewrite H1.
                reflexivity.
             ++ simpl.
                rewrite Nat.ltb_nlt in Hf.
                rewrite Nat.eqb_neq in Hf0.
                rewrite Nat.ltb_nlt in Hf1.
                ifcase (x =? S n).
                ** reflexivity.
                ** simpl.
                   rewrite Nat.eqb_neq in Hf2.
                   assert (~ y < S n) as H0 by omega.
                   rewrite <- Nat.ltb_nlt in H0.
                   rewrite H0.
                   assert (~ y = S n) as H1 by omega.
                   rewrite <- Nat.eqb_neq in H1.
                   rewrite H1.
                   reflexivity.
    - intros N L x y H.
      simpl.
      rewrite IHM1 , IHM2.
      + reflexivity.
      + exact H.
      + exact H.
    - intros N L x y H.
      simpl.
      replace ( shift 0 1 (shift x 1 L) ) with ( shift (S x) 1 (shift 0 1 L) ).
      + replace ( shift 0 1 N [y := L] ) with ( (shift 0 1 N) [S y := shift 0 1 L]).
        * rewrite IHM.
          -- reflexivity.
          -- omega.
        * rewrite shift_lemma03.
          -- reflexivity.
          -- omega.
      + rewrite shift_lemma01.
        * reflexivity.
        * omega.
  Qed.

End Shift_lemmas.

Module Reductions.

  Import Term_shift_substitution.
  
  Inductive beta_reduction : Term -> Term -> Prop :=
  | B1 : forall M N   : Term , beta_reduction (App (Abs M) N) (M [0 := N])
  | B2 : forall M N L : Term , beta_reduction M N -> beta_reduction (App L M) (App L N)
  | B3 : forall M N L : Term , beta_reduction M N -> beta_reduction (App M L) (App N L)
  | B4 : forall M N   : Term , beta_reduction M N -> beta_reduction (Abs M) (Abs N).

  Notation "t --> u" := (beta_reduction t u) (at level 50).

  Inductive beta_reduction_rtclosure : Term -> Term -> Prop :=
  | BBase  : forall M N   : Term , (M --> N) -> (beta_reduction_rtclosure M N)
  | BRefl  : forall M     : Term , beta_reduction_rtclosure M M
  | BTrans : forall M N L : Term , (beta_reduction_rtclosure M N) -> (beta_reduction_rtclosure N L) -> (beta_reduction_rtclosure M L).  

  Notation "t ->> u" := (beta_reduction_rtclosure t u) (at level 50).

  Inductive beta_reduction_parallel : Term -> Term -> Prop :=
  | PB1 : forall x           : nat  , beta_reduction_parallel (Var x) (Var x)
  | PB2 : forall M N         : Term , beta_reduction_parallel M N -> beta_reduction_parallel (Abs M) (Abs N)
  | PB3 : forall M1 N1 M2 N2 : Term , beta_reduction_parallel M1 M2 -> beta_reduction_parallel N1 N2 -> beta_reduction_parallel (App M1 N1) (App M2 N2)
  | PB4 : forall M1 N1 M2 N2 : Term , beta_reduction_parallel M1 M2 -> beta_reduction_parallel N1 N2 -> beta_reduction_parallel (App (Abs M1) N1) (M2 [0 := N2]).

  Notation "==>" := beta_reduction_parallel (at level 100).
  Notation "M ==> N" := (beta_reduction_parallel M N) (at level 50).

End Reductions.

Section Reduction.

  Import Term_shift_substitution.
  Import Reductions.
  
  Lemma beta_reduction_parallel_reflexivity :
    forall M : Term , M ==> M.
  Proof.
    induction M.
    - apply PB1.
    - apply PB3.
      + exact IHM1.
      + exact IHM2.
    - apply PB2.
      exact IHM.
  Qed.

  Lemma beta_reduction_rtclosure_Abs :
    forall M N : Term , M ->> N -> (Abs M) ->> (Abs N).
  Proof.
    intros M N H.
    induction H.
    - apply BBase.
      apply B4.
      exact H.
    - apply BRefl.
    - apply (BTrans (Abs M) (Abs N) (Abs L)).
      + exact IHbeta_reduction_rtclosure1.
      + exact IHbeta_reduction_rtclosure2.
  Qed.


  Lemma beta_reduction_rtclosure_App :
    forall M N L K : Term , M ->> N -> L ->> K -> (App M L) ->> (App N K).
  Proof.
    intros M N L K H0 H1.
    apply (BTrans (App M L) (App M K) (App N K)).
    - induction H1.
      + apply BBase.
        apply B2.
        exact H.
      + exact (BRefl (App M M0)).
      + apply (BTrans (App M M0) (App M N0) (App M L)).
        * exact IHbeta_reduction_rtclosure1.
        * exact IHbeta_reduction_rtclosure2.
    - induction H0.
      + apply BBase.
        apply B3.
        exact H.
      + apply BRefl.
      + apply (BTrans (App M K) (App N K) (App L0 K)).
        * exact IHbeta_reduction_rtclosure1.
        * exact IHbeta_reduction_rtclosure2.
  Qed.

  Lemma beta_reduction_rtclosure_substruction :
    forall M1 N1 M2 N2 : Term , M1 ->> M2 -> N1 ->> N2 -> App (Abs M1) N1 ->> (M2 [0 := N2]).
  Proof.
    intros M1 M2 N1 N2 H0 H1.
    apply (BTrans (App (Abs M1) M2) (App (Abs N1) N2) (N1 [0 := N2])).
    - specialize ((beta_reduction_rtclosure_Abs M1 N1) H0) ; intros H2.
      apply beta_reduction_rtclosure_App.
      + exact H2.
      + exact H1.
    - apply BBase.
      apply B1.
  Qed.

  Proposition beta_reduction_beta_reduction_reduction_parallel :
    forall M N : Term , M --> N -> M ==> N.
  Proof.
    intros M N H.
    induction H.
    - apply PB4.
      + apply beta_reduction_parallel_reflexivity.
      + apply beta_reduction_parallel_reflexivity.
    - apply (PB3 L M L N).
      + apply beta_reduction_parallel_reflexivity.
      + exact IHbeta_reduction.
    - apply (PB3 M L N L).
      + exact IHbeta_reduction.
      + apply beta_reduction_parallel_reflexivity.
    - apply (PB2 M N).
      + exact IHbeta_reduction.
  Qed.

  Proposition beta_reduction_parallel_beta_reduction_reduction_rtclosure :
    forall M N : Term , M ==> N -> M ->> N.
  Proof.
    intros M N H.
    induction H.
    - apply BRefl.
    - apply beta_reduction_rtclosure_Abs.
      exact IHbeta_reduction_parallel.
    - apply beta_reduction_rtclosure_App.
      + exact IHbeta_reduction_parallel1.
      + exact IHbeta_reduction_parallel2.
    - apply beta_reduction_rtclosure_substruction.
      + exact IHbeta_reduction_parallel1.
      + exact IHbeta_reduction_parallel2.
  Qed.

  Proposition beta_reduction_beta_reduction_reduction_rtclosure :
    forall M N : Term , M --> N -> M ->> N.
  Proof.
    intros M N H.
    specialize (BBase M N H).
    intros H2.
    exact H2.
  Qed.

  Lemma beta_reduction_parallel_shift : 
    forall M N : Term , forall x : nat , M ==> N -> shift x 1 M ==> shift x 1 N.
  Proof.
    intros M N x H.
    generalize x.
    induction H.
    - intros x1.
      apply beta_reduction_parallel_reflexivity.
    - intros x0.
      simpl.
      apply PB2.
      apply IHbeta_reduction_parallel.
    - intros x0.
      simpl.
      apply PB3.
      + apply IHbeta_reduction_parallel1.
      + apply IHbeta_reduction_parallel2.
    - intros x0.
      simpl.
      specialize PB4 as H4.
      replace (shift x0 1 M2 [0 := N2]) with (shift (S x0) 1 M2) [0 := ( shift x0 1 N2)].
      + apply PB4.
        * apply IHbeta_reduction_parallel1.
        * apply IHbeta_reduction_parallel2.
      + rewrite <- shift_lemma02.
        * reflexivity.
        * omega.
  Qed.

  Lemma beta_reduction_parallel_substruction :
    forall M1 M2 L1 L2 : Term , forall x : nat , M1 ==> M2 -> L1 ==> L2 -> M1 [x := L1] ==> M2 [x := L2].
  Proof.
    intros M1 M2 L1 L2 x H0 H1.
    generalize H1.
    generalize L1 L2 x.
    induction H0.
    - intros L0 L3 x1.
      simpl.
      ifcase (x1 <? x0).
      + intros H2.
        apply PB1.
      + intros H2.
        ifcase (x1 =? x0).
        * exact H2.
        * apply PB1.
    - intros L0 L3 x0 H2.
      simpl.
      apply PB2.
      apply IHbeta_reduction_parallel.
      apply beta_reduction_parallel_shift.
      exact H2.
    - intros L0 L3 x0 H2.
      simpl.    
      apply PB3.
      + apply IHbeta_reduction_parallel1.
        exact H2.
      + apply IHbeta_reduction_parallel2.
        exact H2.
    - intros L0 L3 x0 H2.
      simpl.
      rewrite <- shift_lemma05.
      + apply PB4.
        -- apply IHbeta_reduction_parallel1.
           apply beta_reduction_parallel_shift.
           exact H2.
        -- apply IHbeta_reduction_parallel2.
           exact H2.
      + omega.
  Qed.

  (* 逆転補題 *)
  Lemma reverse_P12 :
    forall m n : nat,
      Var m ==> Var n -> m = n.
  Proof.
    intros m n H.
    inversion H.
    reflexivity.
  Qed.        

  Lemma reverse_PB2 :
    forall M1 M2 : Term,
      Abs M1 ==> Abs M2 -> M1 ==> M2.
  Proof.
    intros M1 M2 H.
    inversion H.
    exact H2.
  Qed.

  Lemma exists_reverse_PB2 :
    forall M1 M2 : Term,
      Abs M1 ==> M2 -> exists M3 , M2 = Abs M3.
  Proof.
    intros M1 M2 H.
    inversion H.
    exists N.
    reflexivity.
  Qed.

End Reduction.

Section Church_Rosser_Theorem.

  Import Term_shift_substitution.
  Import Reductions.

  Fixpoint beta_reduction_all_parallel (M : Term) : Term :=
    match M with
    | (Var n)     => (Var n)
    | (Abs M1)    => (Abs (beta_reduction_all_parallel M1))
    | (App M1 M2) =>
      match M1 with
      | (Var _)   => (App (beta_reduction_all_parallel M1) (beta_reduction_all_parallel M2))
      | (Abs M11) => (beta_reduction_all_parallel M11) [0 := (beta_reduction_all_parallel M2)]
      | (App _ _) => (App (beta_reduction_all_parallel M1) (beta_reduction_all_parallel M2))
      end
    end.
  
  Lemma Church_Rosser_Lemma1 :
    forall M1 M2 : Term , M1 ==> M2 -> M2 ==> (beta_reduction_all_parallel M1).
  Proof.
    intros M1 M2 H.
    induction H.
    - simpl.
      apply PB1.
    - simpl.
      apply PB2.
      exact IHbeta_reduction_parallel.
    - simpl.
      induction M1.
      + apply PB3.
        * exact IHbeta_reduction_parallel1.
        * exact IHbeta_reduction_parallel2.
      + simpl.
        apply PB3.
        * simpl in IHbeta_reduction_parallel1.
          exact IHbeta_reduction_parallel1.
        * exact IHbeta_reduction_parallel2.
      + specialize (exists_reverse_PB2 M1 M2 H) as H1.
        elim H1.
        intros M3 H2.
        rewrite H2.
        apply PB4.
        * simpl in IHbeta_reduction_parallel1.
          rewrite H2 in IHbeta_reduction_parallel1.
          apply reverse_PB2 in IHbeta_reduction_parallel1.
          exact IHbeta_reduction_parallel1.
        * exact IHbeta_reduction_parallel2.
    - simpl.
      apply beta_reduction_parallel_substruction.
      + exact IHbeta_reduction_parallel1.
      + exact IHbeta_reduction_parallel2.      
  Qed.

  Lemma Church_Rosser_Property_of_beta_reduction_parallel :
    forall M N1 N2 : Term ,
      M ==> N1 /\ M ==> N2 ->
      exists L : Term , N1 ==> L /\ N2 ==> L. 
  Proof.
    intros M N1 N2 H.
    destruct H as [H0 H1].
    exists (beta_reduction_all_parallel M).
    split.
    - apply Church_Rosser_Lemma1.
      exact H0.
    - apply Church_Rosser_Lemma1.
      exact H1.
  Qed.

  Inductive beta_reduction_parallel_RTclosure : Term -> Term -> Prop :=
  | TBRefl  : forall M     : Term , beta_reduction_parallel_RTclosure M M
  | TBTrans : forall M N L : Term , (beta_reduction_parallel_RTclosure M N) -> (beta_reduction_parallel N L) -> (beta_reduction_parallel_RTclosure M L).  

  Lemma another_induction_principle_for_beta_reduction_RTclosure01 : 
    forall M N : Term ,
      beta_reduction_parallel_RTclosure M N -> (M ->> N).
  Proof.
    intros M N H.
    induction H.
    - apply BRefl.
    - apply beta_reduction_parallel_beta_reduction_reduction_rtclosure in H0.
      exact (BTrans M N L IHbeta_reduction_parallel_RTclosure H0).
  Qed.

  Lemma another_induction_principle_for_beta_reduction_RTclosure02 : 
    forall M N : Term ,
      (M ->> N) -> beta_reduction_parallel_RTclosure M N.
  Proof.
    intros M N H.
    induction H.
    - apply beta_reduction_beta_reduction_reduction_parallel in H.
      apply (TBTrans M M N).
      + apply TBRefl.
      + exact H.
    - apply TBRefl.
    - assert (exists N' , beta_reduction_parallel_RTclosure M N' /\ N' ==> L) as H1.
      + induction IHbeta_reduction_rtclosure2.
        * exists M0.
          split.
          -- exact IHbeta_reduction_rtclosure1.
          -- apply beta_reduction_parallel_reflexivity.
        * exists N.
          split.
          -- apply another_induction_principle_for_beta_reduction_RTclosure01 in IHbeta_reduction_rtclosure2.
             specialize (IHIHbeta_reduction_rtclosure2 H IHbeta_reduction_rtclosure2 IHbeta_reduction_rtclosure1) as H2.
             elim H2.
             intros L' H3.
             destruct H3 as [H30 H31].
             exact (TBTrans M L' N H30 H31).
          -- exact H1.
      + elim H1.
        intros L' H2.
        destruct H2 as [H20 H21].
        exact (TBTrans M L' L H20 H21).
  Qed.

  Lemma CH_para_toto :
    forall M N0 N1 : Term,
      M ==> N0 /\ M ->> N1 ->
      exists L , N0 ->> L /\ N1 ==> L.
  Proof.
    intros M N0 N1 H.
    destruct H as [H0 H1].
    specialize (another_induction_principle_for_beta_reduction_RTclosure02 M N1 H1) as H2.
    induction H2.
    - exists N0.
      split.
      + apply BRefl.
      + exact H0.
    - specialize (IHbeta_reduction_parallel_RTclosure H0 (another_induction_principle_for_beta_reduction_RTclosure01 M N H2)) as H3.
      elim H3.
      intros L' H4.
      destruct H4 as [H40 H41].
      specialize (Church_Rosser_Property_of_beta_reduction_parallel N L L' (conj H H41)) as H5.
      elim H5.
      intros K H6.
      destruct H6 as [H60 H61].
      exists K.
      split.
      + specialize (beta_reduction_parallel_beta_reduction_reduction_rtclosure L' K H61) as H610.
        exact (BTrans N0 L' K H40 H610).
      + exact H60.
  Qed.
  
  Theorem Church_Rosser_Theorem :
    forall M N1 N2 : Term , 
      M ->> N1 -> M ->> N2 ->
      exists L : Term ,  N1 ->> L /\ N2 ->> L.
  Proof.
    intros M N1 N2 H0.
    generalize N2 as N0.
    apply another_induction_principle_for_beta_reduction_RTclosure02 in H0.
    induction H0.
    - intros N0 H0.
      exists N0.
      split.
      + exact H0.
      + apply BRefl.
    - intros N0 H1.
      specialize (IHbeta_reduction_parallel_RTclosure N0 H1) as H2.
      elim H2.
      intros L' H3.
      destruct H3 as [H30 H31].
      specialize (CH_para_toto N L L' (conj H H30)) as H4.
      elim H4.
      intros K H5.
      destruct H5 as [H50 H51].
      exists K.
      split.
      + exact H50.
      + exact (BTrans N0 L' K H31 (beta_reduction_parallel_beta_reduction_reduction_rtclosure L' K H51)).
  Qed.

End Church_Rosser_Theorem.
