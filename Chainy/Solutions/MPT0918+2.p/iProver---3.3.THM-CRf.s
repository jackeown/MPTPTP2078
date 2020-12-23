%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0918+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 27.79s
% Output     : CNFRefutation 27.79s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 359 expanded)
%              Number of clauses        :   34 (  47 expanded)
%              Number of leaves         :    9 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  347 (1848 expanded)
%              Number of equality atoms :  318 (1692 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1386,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1387,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
       => ~ ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f1386])).

fof(f2796,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1387])).

fof(f2797,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f2796])).

fof(f3873,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
     => ( ( k11_mcart_1(X0,X1,X2,X3,X4) != sK439
          | k10_mcart_1(X0,X1,X2,X3,X4) != sK438
          | k9_mcart_1(X0,X1,X2,X3,X4) != sK437
          | k8_mcart_1(X0,X1,X2,X3,X4) != sK436 )
        & k4_mcart_1(sK436,sK437,sK438,sK439) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f3872,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5,X6,X7,X8] :
            ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
              | k10_mcart_1(X0,X1,X2,X3,X4) != X7
              | k9_mcart_1(X0,X1,X2,X3,X4) != X6
              | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( ? [X8,X7,X6,X5] :
          ( ( k11_mcart_1(sK431,sK432,sK433,sK434,sK435) != X8
            | k10_mcart_1(sK431,sK432,sK433,sK434,sK435) != X7
            | k9_mcart_1(sK431,sK432,sK433,sK434,sK435) != X6
            | k8_mcart_1(sK431,sK432,sK433,sK434,sK435) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = sK435 )
      & k1_xboole_0 != sK434
      & k1_xboole_0 != sK433
      & k1_xboole_0 != sK432
      & k1_xboole_0 != sK431
      & m1_subset_1(sK435,k4_zfmisc_1(sK431,sK432,sK433,sK434)) ) ),
    introduced(choice_axiom,[])).

fof(f3874,plain,
    ( ( k11_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK439
      | k10_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK438
      | k9_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK437
      | k8_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK436 )
    & k4_mcart_1(sK436,sK437,sK438,sK439) = sK435
    & k1_xboole_0 != sK434
    & k1_xboole_0 != sK433
    & k1_xboole_0 != sK432
    & k1_xboole_0 != sK431
    & m1_subset_1(sK435,k4_zfmisc_1(sK431,sK432,sK433,sK434)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK431,sK432,sK433,sK434,sK435,sK436,sK437,sK438,sK439])],[f2797,f3873,f3872])).

fof(f6348,plain,(
    m1_subset_1(sK435,k4_zfmisc_1(sK431,sK432,sK433,sK434)) ),
    inference(cnf_transformation,[],[f3874])).

fof(f1279,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6082,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1279])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6080,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f6371,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6082,f6080])).

fof(f7254,plain,(
    m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK431,sK432),sK433),sK434)) ),
    inference(definition_unfolding,[],[f6348,f6371])).

fof(f6353,plain,(
    k4_mcart_1(sK436,sK437,sK438,sK439) = sK435 ),
    inference(cnf_transformation,[],[f3874])).

fof(f1278,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6081,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1276,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6079,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1276])).

fof(f6372,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6081,f6079])).

fof(f7249,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK436,sK437),sK438),sK439) = sK435 ),
    inference(definition_unfolding,[],[f6353,f6372])).

fof(f1365,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2769,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              | k4_mcart_1(X5,X6,X7,X8) != X4 )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1365])).

fof(f6283,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2769])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3884,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7183,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6283,f6372,f6371,f3884,f3884,f3884,f3884])).

fof(f7542,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7183])).

fof(f6354,plain,
    ( k11_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK439
    | k10_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK438
    | k9_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK437
    | k8_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK436 ),
    inference(cnf_transformation,[],[f3874])).

fof(f6280,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2769])).

fof(f7186,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6280,f6372,f6371,f3884,f3884,f3884,f3884])).

fof(f7545,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7186])).

fof(f6281,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2769])).

fof(f7185,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6281,f6372,f6371,f3884,f3884,f3884,f3884])).

fof(f7544,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7185])).

fof(f6282,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2769])).

fof(f7184,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6282,f6372,f6371,f3884,f3884,f3884,f3884])).

fof(f7543,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7184])).

fof(f6352,plain,(
    k1_xboole_0 != sK434 ),
    inference(cnf_transformation,[],[f3874])).

fof(f7250,plain,(
    o_0_0_xboole_0 != sK434 ),
    inference(definition_unfolding,[],[f6352,f3884])).

fof(f6351,plain,(
    k1_xboole_0 != sK433 ),
    inference(cnf_transformation,[],[f3874])).

fof(f7251,plain,(
    o_0_0_xboole_0 != sK433 ),
    inference(definition_unfolding,[],[f6351,f3884])).

fof(f6350,plain,(
    k1_xboole_0 != sK432 ),
    inference(cnf_transformation,[],[f3874])).

fof(f7252,plain,(
    o_0_0_xboole_0 != sK432 ),
    inference(definition_unfolding,[],[f6350,f3884])).

fof(f6349,plain,(
    k1_xboole_0 != sK431 ),
    inference(cnf_transformation,[],[f3874])).

fof(f7253,plain,(
    o_0_0_xboole_0 != sK431 ),
    inference(definition_unfolding,[],[f6349,f3884])).

cnf(c_2458,negated_conjecture,
    ( m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK431,sK432),sK433),sK434)) ),
    inference(cnf_transformation,[],[f7254])).

cnf(c_69632,plain,
    ( m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK431,sK432),sK433),sK434)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2458])).

cnf(c_2453,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(sK436,sK437),sK438),sK439) = sK435 ),
    inference(cnf_transformation,[],[f7249])).

cnf(c_2384,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k11_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X3
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X7 ),
    inference(cnf_transformation,[],[f7542])).

cnf(c_69696,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_91413,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK436,sK437),sK438),sK439)) = sK439
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_69696])).

cnf(c_91452,plain,
    ( k11_mcart_1(X0,X1,X2,X3,sK435) = sK439
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91413,c_2453])).

cnf(c_91518,plain,
    ( k11_mcart_1(sK431,sK432,sK433,sK434,sK435) = sK439
    | sK434 = o_0_0_xboole_0
    | sK433 = o_0_0_xboole_0
    | sK432 = o_0_0_xboole_0
    | sK431 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_69632,c_91452])).

cnf(c_2452,negated_conjecture,
    ( k9_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK437
    | k8_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK436
    | k11_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK439
    | k10_mcart_1(sK431,sK432,sK433,sK434,sK435) != sK438 ),
    inference(cnf_transformation,[],[f6354])).

cnf(c_2387,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k8_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X0
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X7 ),
    inference(cnf_transformation,[],[f7545])).

cnf(c_69693,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_90235,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK436,sK437),sK438),sK439)) = sK436
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_69693])).

cnf(c_90270,plain,
    ( k8_mcart_1(X0,X1,X2,X3,sK435) = sK436
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_90235,c_2453])).

cnf(c_90327,plain,
    ( k8_mcart_1(sK431,sK432,sK433,sK434,sK435) = sK436
    | sK434 = o_0_0_xboole_0
    | sK433 = o_0_0_xboole_0
    | sK432 = o_0_0_xboole_0
    | sK431 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_69632,c_90270])).

cnf(c_2386,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k9_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X1
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X7 ),
    inference(cnf_transformation,[],[f7544])).

cnf(c_69694,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2386])).

cnf(c_90490,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK436,sK437),sK438),sK439)) = sK437
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_69694])).

cnf(c_90525,plain,
    ( k9_mcart_1(X0,X1,X2,X3,sK435) = sK437
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_90490,c_2453])).

cnf(c_90653,plain,
    ( k9_mcart_1(sK431,sK432,sK433,sK434,sK435) = sK437
    | sK434 = o_0_0_xboole_0
    | sK433 = o_0_0_xboole_0
    | sK432 = o_0_0_xboole_0
    | sK431 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_69632,c_90525])).

cnf(c_2385,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k10_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X2
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X7 ),
    inference(cnf_transformation,[],[f7543])).

cnf(c_69695,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2385])).

cnf(c_90856,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK436,sK437),sK438),sK439)) = sK438
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_69695])).

cnf(c_90891,plain,
    ( k10_mcart_1(X0,X1,X2,X3,sK435) = sK438
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK435,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_90856,c_2453])).

cnf(c_91217,plain,
    ( k10_mcart_1(sK431,sK432,sK433,sK434,sK435) = sK438
    | sK434 = o_0_0_xboole_0
    | sK433 = o_0_0_xboole_0
    | sK432 = o_0_0_xboole_0
    | sK431 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_69632,c_90891])).

cnf(c_91573,plain,
    ( sK434 = o_0_0_xboole_0
    | sK433 = o_0_0_xboole_0
    | sK432 = o_0_0_xboole_0
    | sK431 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_91518,c_2452,c_90327,c_90653,c_91217])).

cnf(c_2454,negated_conjecture,
    ( o_0_0_xboole_0 != sK434 ),
    inference(cnf_transformation,[],[f7250])).

cnf(c_91584,plain,
    ( sK433 = o_0_0_xboole_0
    | sK432 = o_0_0_xboole_0
    | sK431 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_91573,c_2454])).

cnf(c_2455,negated_conjecture,
    ( o_0_0_xboole_0 != sK433 ),
    inference(cnf_transformation,[],[f7251])).

cnf(c_91698,plain,
    ( sK432 = o_0_0_xboole_0
    | sK431 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_91584,c_2455])).

cnf(c_2456,negated_conjecture,
    ( o_0_0_xboole_0 != sK432 ),
    inference(cnf_transformation,[],[f7252])).

cnf(c_91714,plain,
    ( sK431 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_91698,c_2456])).

cnf(c_2457,negated_conjecture,
    ( o_0_0_xboole_0 != sK431 ),
    inference(cnf_transformation,[],[f7253])).

cnf(c_92004,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_91714,c_2457])).

cnf(c_92005,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_92004])).

%------------------------------------------------------------------------------
