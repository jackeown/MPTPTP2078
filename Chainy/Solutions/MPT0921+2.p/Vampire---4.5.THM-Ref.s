%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0921+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 2.43s
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
fof(f4884,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4883,f4834])).

fof(f4834,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4832,f2978])).

fof(f2978,plain,(
    m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(cnf_transformation,[],[f2334])).

fof(f2334,plain,
    ( sK22 != k10_mcart_1(sK18,sK19,sK20,sK21,sK23)
    & k1_xboole_0 != sK21
    & k1_xboole_0 != sK20
    & k1_xboole_0 != sK19
    & k1_xboole_0 != sK18
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK22 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != sK23
                    | ~ m1_subset_1(X9,sK21) )
                | ~ m1_subset_1(X8,sK20) )
            | ~ m1_subset_1(X7,sK19) )
        | ~ m1_subset_1(X6,sK18) )
    & m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22,sK23])],[f1429,f2333])).

fof(f2333,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X8
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK22 != k10_mcart_1(sK18,sK19,sK20,sK21,sK23)
      & k1_xboole_0 != sK21
      & k1_xboole_0 != sK20
      & k1_xboole_0 != sK19
      & k1_xboole_0 != sK18
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK22 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != sK23
                      | ~ m1_subset_1(X9,sK21) )
                  | ~ m1_subset_1(X8,sK20) )
              | ~ m1_subset_1(X7,sK19) )
          | ~ m1_subset_1(X6,sK18) )
      & m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ) ),
    introduced(choice_axiom,[])).

fof(f1429,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f1428])).

fof(f1428,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1391])).

fof(f1391,negated_conjecture,(
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
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1390])).

fof(f1390,conjecture,(
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
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f4832,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3328,f4759])).

fof(f4759,plain,(
    k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(subsumption_resolution,[],[f4758,f2980])).

fof(f2980,plain,(
    k1_xboole_0 != sK18 ),
    inference(cnf_transformation,[],[f2334])).

fof(f4758,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4757,f2981])).

fof(f2981,plain,(
    k1_xboole_0 != sK19 ),
    inference(cnf_transformation,[],[f2334])).

fof(f4757,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4756,f2982])).

fof(f2982,plain,(
    k1_xboole_0 != sK20 ),
    inference(cnf_transformation,[],[f2334])).

fof(f4756,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4738,f2983])).

fof(f2983,plain,(
    k1_xboole_0 != sK21 ),
    inference(cnf_transformation,[],[f2334])).

fof(f4738,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK23) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2978,f2997])).

fof(f2997,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1435,plain,(
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

fof(f3328,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1597])).

fof(f1597,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1296])).

fof(f1296,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f4883,plain,(
    ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4882,f4842])).

fof(f4842,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19) ),
    inference(subsumption_resolution,[],[f4840,f2978])).

fof(f4840,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3327,f4763])).

fof(f4763,plain,(
    k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))) ),
    inference(subsumption_resolution,[],[f4762,f2980])).

fof(f4762,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4761,f2981])).

fof(f4761,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4760,f2982])).

fof(f4760,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4739,f2983])).

fof(f4739,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23)))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2978,f2998])).

fof(f2998,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f3327,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1596])).

fof(f1596,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f4882,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4881,f4828])).

fof(f4828,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20) ),
    inference(subsumption_resolution,[],[f4822,f2978])).

fof(f4822,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f2989,f4767])).

fof(f4767,plain,(
    k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23)) ),
    inference(subsumption_resolution,[],[f4766,f2980])).

fof(f4766,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4765,f2981])).

fof(f4765,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4764,f2982])).

fof(f4764,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4740,f2983])).

fof(f4740,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(k1_mcart_1(sK23))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2978,f2999])).

fof(f2999,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f2989,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1432])).

fof(f1432,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f4881,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4880,f4814])).

fof(f4814,plain,(
    m1_subset_1(k2_mcart_1(sK23),sK21) ),
    inference(subsumption_resolution,[],[f4812,f2978])).

fof(f4812,plain,
    ( m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(sK23,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(superposition,[],[f3329,f4772])).

fof(f4772,plain,(
    k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23) ),
    inference(subsumption_resolution,[],[f4771,f2980])).

fof(f4771,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4770,f2981])).

fof(f4770,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4769,f2982])).

fof(f4769,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4741,f2983])).

fof(f4741,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK23) = k2_mcart_1(sK23)
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2978,f3000])).

fof(f3000,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f3329,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f1598])).

fof(f1598,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f4880,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(subsumption_resolution,[],[f4879,f4820])).

fof(f4820,plain,(
    sK22 != k2_mcart_1(k1_mcart_1(sK23)) ),
    inference(superposition,[],[f2984,f4767])).

fof(f2984,plain,(
    sK22 != k10_mcart_1(sK18,sK19,sK20,sK21,sK23) ),
    inference(cnf_transformation,[],[f2334])).

fof(f4879,plain,
    ( sK22 = k2_mcart_1(k1_mcart_1(sK23))
    | ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(trivial_inequality_removal,[],[f4856])).

fof(f4856,plain,
    ( sK23 != sK23
    | sK22 = k2_mcart_1(k1_mcart_1(sK23))
    | ~ m1_subset_1(k2_mcart_1(sK23),sK21)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK23)),sK20)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK19)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),sK18) ),
    inference(superposition,[],[f2979,f4780])).

fof(f4780,plain,(
    sK23 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4779,f4759])).

fof(f4779,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK23))),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4778,f4763])).

fof(f4778,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(k1_mcart_1(sK23)),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4777,f4767])).

fof(f4777,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k2_mcart_1(sK23)) ),
    inference(forward_demodulation,[],[f4776,f4772])).

fof(f4776,plain,(
    sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23)) ),
    inference(subsumption_resolution,[],[f4775,f2980])).

fof(f4775,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4774,f2981])).

fof(f4774,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4773,f2982])).

fof(f4773,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4742,f2983])).

fof(f4742,plain,
    ( sK23 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK23),k9_mcart_1(sK18,sK19,sK20,sK21,sK23),k10_mcart_1(sK18,sK19,sK20,sK21,sK23),k11_mcart_1(sK18,sK19,sK20,sK21,sK23))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2978,f3005])).

fof(f3005,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1437])).

fof(f1437,plain,(
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

fof(f2979,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK23
      | sK22 = X8
      | ~ m1_subset_1(X9,sK21)
      | ~ m1_subset_1(X8,sK20)
      | ~ m1_subset_1(X7,sK19)
      | ~ m1_subset_1(X6,sK18) ) ),
    inference(cnf_transformation,[],[f2334])).
%------------------------------------------------------------------------------
