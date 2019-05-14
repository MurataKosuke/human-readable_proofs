Lemma beta_reduction_parallel_substruction :
  forall M1 M2 L1 L2 : Term ,
  forall x : nat ,
    M1 ==> M2 -> L1 ==> L2 -> (M1 [x := L1] ==> (M2 [x := L2])).
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
    Left
    = (Abs M [x0 := L0]).
    = (Abs (M [S x0 := shift 0 1 L0]))    { bydef }.
    < beta_reduction_parallel > (Abs (N [S x0 := shift 0 1 L3]))
                                  { apply (PB2 (M [S x0 := shift 0 1 L0])
                                               (N [S x0 := shift 0 1 L3])
                                               (IHbeta_reduction_parallel
                                                  (shift 0 1 L0)
                                                  (shift 0 1 L3)
                                                  (S x0)
                                                  (beta_reduction_parallel_shift L0 L3 0 H2)
                                               )
                                          )
                                  }.
    = ((Abs N) [x0 := L3])    { bydef }.
    = Right.
  - intros L0 L3 x0 H.
    Left
    = ((App M1 N1) [x0 := L0]).
    = (App (M1 [x0 := L0]) (N1 [x0 := L0])).
    < beta_reduction_parallel > (App (M2 [x0 := L3]) (N2 [x0 := L3]))
                                  { exact
                                      (PB3 (M1 [x0 := L0]) (N1 [x0 := L0]) (M2 [x0 := L3]) (N2 [x0 := L3])
                                           (IHbeta_reduction_parallel1 L0 L3 x0 H)
                                           (IHbeta_reduction_parallel2 L0 L3 x0 H))
                                  }.
    = ((App M2 N2) [x0 := L3])  { bydef }.
    = Right.
  - intros L0 L3 x0 H.
    Left
    = ((App (Abs M1) N1) [x0 := L0]).
    = (App (Abs M1 [S x0 := shift 0 1 L0]) (N1 [x0 := L0])).
    Check PB4.
    < beta_reduction_parallel > ((M2 [S x0 := shift 0 1 L3]) [0 := N2 [x0 := L3]])
                                  { apply
                                      (PB4
                                         (M1 [S x0 := shift 0 1 L0])
                                         (N1 [x0 := L0])
                                         (M2 [S x0 := shift 0 1 L3])
                                         (N2 [x0 := L3])
                                         (IHbeta_reduction_parallel1
                                            (shift 0 1 L0)
                                            (shift 0 1 L3)
                                            (S x0)
                                            (
                                              beta_reduction_parallel_shift L0 L3 0 H
                                            )
                                         )
                                         (IHbeta_reduction_parallel2
                                            L0
                                            L3
                                            x0
                                            H
                                         )
                                      )
                                  }.
    = ((M2 [0 := N2]) [x0 := L3])    { rewrite shift_lemma05 ; [idtac | omega] }.
    = Right.
Qed.
