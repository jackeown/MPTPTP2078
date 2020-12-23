%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0919+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.80s
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
fof(f4847,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4846,f4799])).

fof(f4799,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4793,f2962])).

fof(f2962,plain,(
    m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(cnf_transformation,[],[f2328])).

fof(f2328,plain,
    ( sK22 != k8_mcart_1(sK18,sK19,sK20,sK21,sK23)
    & k1_xboole_0 != sK21
    & k1_xboole_0 != sK20
    & k1_xboole_0 != sK19
    & k1_xboole_0 != sK18
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK22 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != sK23
                    | ~ m1_subset_1(X9,sK21) )
                | ~ m1_subset_1(X8,sK20) )
            | ~ m1_subset_1(X7,sK19) )
        | ~ m1_subset_1(X6,sK18) )
    & m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22,sK23])],[f1427,f2327])).

fof(f2327,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X6
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK22 != k8_mcart_1(sK18,sK19,sK20,sK21,sK23)
      & k1_xboole_0 != sK21
      & k1_xboole_0 != sK20
      & k1_xboole_0 != sK19
      & k1_xboole_0 != sK18
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK22 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != sK23
                      | ~ m1_subset_1(X9,sK21) )
                  | ~ m1_subset_1(X8,sK20) )
              | ~ m1_subset_1(X7,sK19) )
          | ~ m1_subset_1(X6,sK18) )
      & m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ) ),
    introduced(choice_axiom,[])).

fof(f1427,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f1426])).

fof(f1426,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1388])).

fof(f1388,negated_conjecture,(
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
                           => X4 = X6 ) ) ) ) )
         => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1387])).

fof(f1387,conjecture,(
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
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f4793,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f2973,f4729])).

fof(f4729,plain,(
    k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(subsumption_resolution,[],[f4728,f2964])).

fof(f2964,plain,(
    k1_xboole_0 != sK18 ),
    inference(cnf_transformation,[],[f2328])).

fof(f4728,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4727,f2965])).

fof(f2965,plain,(
    k1_xboole_0 != sK19 ),
    inference(cnf_transformation,[],[f2328])).

fof(f4727,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4726,f2966])).

fof(f2966,plain,(
    k1_xboole_0 != sK20 ),
    inference(cnf_transformation,[],[f2328])).

fof(f4726,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4710,f2967])).

fof(f2967,plain,(
    k1_xboole_0 != sK21 ),
    inference(cnf_transformation,[],[f2328])).

fof(f4710,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2962,f2981])).

fof(f2981,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1433])).

fof(f1433,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f2973,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1296])).

fof(f1296,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f4846,plain,(
    ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4845,f4802])).

fof(f4802,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19) ),
    inference(subsumption_resolution,[],[f4800,f2962])).

fof(f4800,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3301,f4734])).

fof(f4734,plain,(
    k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(subsumption_resolution,[],[f4733,f2964])).

fof(f4733,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4732,f2965])).

fof(f4732,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4731,f2966])).

fof(f4731,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4711,f2967])).

fof(f4711,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2962,f2982])).

fof(f2982,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1433])).

fof(f3301,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1592])).

fof(f1592,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f4845,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4844,f4782])).

fof(f4782,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20) ),
    inference(subsumption_resolution,[],[f4780,f2962])).

fof(f4780,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3300,f4738])).

fof(f4738,plain,(
    k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23)) ),
    inference(subsumption_resolution,[],[f4737,f2964])).

fof(f4737,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4736,f2965])).

fof(f4736,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4735,f2966])).

fof(f4735,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4712,f2967])).

fof(f4712,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2962,f2983])).

fof(f2983,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1433])).

fof(f3300,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1591])).

fof(f1591,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f4844,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4843,f4774])).

fof(f4774,plain,(
    m1_subset_1(k2_mcart_1(sK23),sK21) ),
    inference(subsumption_resolution,[],[f4772,f2962])).

fof(f4772,plain,
    ( m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3299,f4742])).

fof(f4742,plain,(
    k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23) ),
    inference(subsumption_resolution,[],[f4741,f2964])).

fof(f4741,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4740,f2965])).

fof(f4740,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4739,f2966])).

fof(f4739,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4713,f2967])).

fof(f4713,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2962,f2984])).

fof(f2984,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1433])).

fof(f3299,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1590])).

fof(f1590,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f4843,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4842,f4791])).

fof(f4791,plain,(
    sK22 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(superposition,[],[f2968,f4729])).

fof(f2968,plain,(
    sK22 != k8_mcart_1(sK18,sK19,sK20,sK21,sK23) ),
    inference(cnf_transformation,[],[f2328])).

fof(f4842,plain,
    ( sK22 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(trivial_inequality_removal,[],[f4819])).

fof(f4819,plain,
    ( sK23 != sK23
    | sK22 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(superposition,[],[f2963,f4750])).

fof(f4750,plain,(
    sK23 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4749,f4729])).

fof(f4749,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4748,f4734])).

fof(f4748,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4747,f4738])).

fof(f4747,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4746,f4742])).

fof(f4746,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23)) ),
    inference(subsumption_resolution,[],[f4745,f2964])).

fof(f4745,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4744,f2965])).

fof(f4744,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4743,f2966])).

fof(f4743,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4714,f2967])).

fof(f4714,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2962,f2989])).

fof(f2989,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1435,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f2963,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK23
      | sK22 = X6
      | ~ m1_subset_1(X9,sK21)
      | ~ m1_subset_1(X8,sK20)
      | ~ m1_subset_1(X7,sK19)
      | ~ m1_subset_1(X6,sK18) ) ),
    inference(cnf_transformation,[],[f2328])).
%------------------------------------------------------------------------------
