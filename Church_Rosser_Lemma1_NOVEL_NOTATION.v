Lemma Church_Rosser_Lemma1 :
  forall M1 M2 : Term , M1 ==> M2 -> M2 ==> (beta_reduction_all_parallel M1).
Proof.
  intros M1 M2 H.
  induction H.
  - Left
    = (Var x).
    <beta_reduction_parallel> (beta_reduction_all_parallel (Var x)) { apply PB1 }.
    = Right.
  - Left
    = (Abs N).
    <beta_reduction_parallel> (Abs (beta_reduction_all_parallel M))
                                { exact (PB2
                                           N
                                           (beta_reduction_all_parallel M)
                                           IHbeta_reduction_parallel
                                        )
                                }.
    = (beta_reduction_all_parallel (Abs M)).
    = Right.
  - induction M1.
    + Left
      = (App M2 N2).
      <beta_reduction_parallel> (beta_reduction_all_parallel (App (Var n) N1))
                                  {
                                    exact (PB3
                                             M2
                                             N2
                                             (beta_reduction_all_parallel  (Var n))
                                             (beta_reduction_all_parallel N1)
                                             IHbeta_reduction_parallel1
                                             IHbeta_reduction_parallel2
                                          )
                                  }.
      = Right.
    + Left
      = (App M2 N2).
      <beta_reduction_parallel> ( beta_reduction_all_parallel (App (App M1_1 M1_2) N1) )
                                  {
                                    exact (PB3
                                             M2
                                             N2
                                             (beta_reduction_all_parallel (App M1_1 M1_2))
                                             (beta_reduction_all_parallel N1)
                                             IHbeta_reduction_parallel1
                                             IHbeta_reduction_parallel2
                                          )
                                  }.
      = Right.
    + specialize (exists_reverse_PB2 M1 M2 H) as H1.
      elim H1 ; intros M3 H2 ; rewrite H2.
      Left
      = (App (Abs M3) N2).
      <beta_reduction_parallel> ( beta_reduction_all_parallel (App (Abs M1) N1) )
                                  {
                                    rewrite H2 in IHbeta_reduction_parallel1 ;
                                    apply reverse_PB2 in IHbeta_reduction_parallel1 ;
                                    exact (PB4
                                             M3
                                             N2
                                             (beta_reduction_all_parallel M1)
                                             (beta_reduction_all_parallel N1)
                                             IHbeta_reduction_parallel1
                                             IHbeta_reduction_parallel2 
                                          )
                                  }.
      = Right.
  - Left
    = (M2 [0 := N2]).
    <beta_reduction_parallel> ( beta_reduction_all_parallel (App (Abs M1) N1) )
                                {
                                  exact ( beta_reduction_parallel_substruction
                                            M2
                                            (beta_reduction_all_parallel M1)
                                            N2
                                            (beta_reduction_all_parallel N1)
                                            0
                                            IHbeta_reduction_parallel1
                                            IHbeta_reduction_parallel2
                                        )
                                }.
    = Right.
Qed.
