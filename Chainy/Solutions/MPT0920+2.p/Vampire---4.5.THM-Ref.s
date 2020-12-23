%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0920+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 504 expanded)
%              Number of leaves         :    8 ( 126 expanded)
%              Depth                    :   21
%              Number of atoms          :  294 (5212 expanded)
%              Number of equality atoms :  190 (3149 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4867,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4866,f4813])).

fof(f4813,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4811,f2970])).

fof(f2970,plain,(
    m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(cnf_transformation,[],[f2331])).

fof(f2331,plain,
    ( sK22 != k9_mcart_1(sK18,sK19,sK20,sK21,sK23)
    & k1_xboole_0 != sK21
    & k1_xboole_0 != sK20
    & k1_xboole_0 != sK19
    & k1_xboole_0 != sK18
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK22 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != sK23
                    | ~ m1_subset_1(X9,sK21) )
                | ~ m1_subset_1(X8,sK20) )
            | ~ m1_subset_1(X7,sK19) )
        | ~ m1_subset_1(X6,sK18) )
    & m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22,sK23])],[f1428,f2330])).

fof(f2330,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X7
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK22 != k9_mcart_1(sK18,sK19,sK20,sK21,sK23)
      & k1_xboole_0 != sK21
      & k1_xboole_0 != sK20
      & k1_xboole_0 != sK19
      & k1_xboole_0 != sK18
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK22 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != sK23
                      | ~ m1_subset_1(X9,sK21) )
                  | ~ m1_subset_1(X8,sK20) )
              | ~ m1_subset_1(X7,sK19) )
          | ~ m1_subset_1(X6,sK18) )
      & m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ) ),
    introduced(choice_axiom,[])).

fof(f1428,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f1427])).

fof(f1427,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1390])).

fof(f1390,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X7 ) ) ) ) )
         => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1389])).

fof(f1389,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f4811,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3313,f4744])).

fof(f4744,plain,(
    k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(subsumption_resolution,[],[f4743,f2972])).

fof(f2972,plain,(
    k1_xboole_0 != sK18 ),
    inference(cnf_transformation,[],[f2331])).

fof(f4743,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4742,f2973])).

fof(f2973,plain,(
    k1_xboole_0 != sK19 ),
    inference(cnf_transformation,[],[f2331])).

fof(f4742,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4741,f2974])).

fof(f2974,plain,(
    k1_xboole_0 != sK20 ),
    inference(cnf_transformation,[],[f2331])).

fof(f4741,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4724,f2975])).

fof(f2975,plain,(
    k1_xboole_0 != sK21 ),
    inference(cnf_transformation,[],[f2331])).

fof(f4724,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2970,f2989])).

fof(f2989,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1434])).

fof(f1434,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1368])).

fof(f1368,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f3313,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1593])).

fof(f1593,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1296])).

fof(f1296,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f4866,plain,(
    ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4865,f4827])).

fof(f4827,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19) ),
    inference(subsumption_resolution,[],[f4821,f2970])).

fof(f4821,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f2981,f4748])).

fof(f4748,plain,(
    k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(subsumption_resolution,[],[f4747,f2972])).

fof(f4747,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4746,f2973])).

fof(f4746,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4745,f2974])).

fof(f4745,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4725,f2975])).

fof(f4725,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2970,f2990])).

fof(f2990,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1434])).

fof(f2981,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1431])).

fof(f1431,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f4865,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4864,f4802])).

fof(f4802,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20) ),
    inference(subsumption_resolution,[],[f4800,f2970])).

fof(f4800,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3315,f4753])).

fof(f4753,plain,(
    k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23)) ),
    inference(subsumption_resolution,[],[f4752,f2972])).

fof(f4752,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4751,f2973])).

fof(f4751,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4750,f2974])).

fof(f4750,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4726,f2975])).

fof(f4726,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2970,f2991])).

fof(f2991,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1434])).

fof(f3315,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1595])).

fof(f1595,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f4864,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4863,f4794])).

fof(f4794,plain,(
    m1_subset_1(k2_mcart_1(sK23),sK21) ),
    inference(subsumption_resolution,[],[f4792,f2970])).

fof(f4792,plain,
    ( m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3314,f4757])).

fof(f4757,plain,(
    k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23) ),
    inference(subsumption_resolution,[],[f4756,f2972])).

fof(f4756,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4755,f2973])).

fof(f4755,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4754,f2974])).

fof(f4754,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4727,f2975])).

fof(f4727,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2970,f2992])).

fof(f2992,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1434])).

fof(f3314,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1594])).

fof(f1594,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f4863,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4862,f4819])).

fof(f4819,plain,(
    sK22 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(superposition,[],[f2976,f4748])).

fof(f2976,plain,(
    sK22 != k9_mcart_1(sK18,sK19,sK20,sK21,sK23) ),
    inference(cnf_transformation,[],[f2331])).

fof(f4862,plain,
    ( sK22 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(trivial_inequality_removal,[],[f4839])).

fof(f4839,plain,
    ( sK23 != sK23
    | sK22 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(superposition,[],[f2971,f4765])).

fof(f4765,plain,(
    sK23 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4764,f4744])).

fof(f4764,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4763,f4748])).

fof(f4763,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4762,f4753])).

fof(f4762,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4761,f4757])).

fof(f4761,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23)) ),
    inference(subsumption_resolution,[],[f4760,f2972])).

fof(f4760,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4759,f2973])).

fof(f4759,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4758,f2974])).

fof(f4758,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4728,f2975])).

fof(f4728,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2970,f2997])).

fof(f2997,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1436])).

fof(f1436,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1367])).

fof(f1367,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f2971,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK23
      | sK22 = X7
      | ~ m1_subset_1(X9,sK21)
      | ~ m1_subset_1(X8,sK20)
      | ~ m1_subset_1(X7,sK19)
      | ~ m1_subset_1(X6,sK18) ) ),
    inference(cnf_transformation,[],[f2331])).
%------------------------------------------------------------------------------
