%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0887+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 27.74s
% Output     : CNFRefutation 27.74s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 265 expanded)
%              Number of clauses        :   38 (  47 expanded)
%              Number of leaves         :   16 (  91 expanded)
%              Depth                    :   21
%              Number of atoms          :  486 (1355 expanded)
%              Number of equality atoms :  384 (1151 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1340,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1341,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ? [X3] :
              ( ? [X4,X5,X6] :
                  ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                      & k6_mcart_1(X0,X1,X2,X3) = X5
                      & k5_mcart_1(X0,X1,X2,X3) = X4 )
                  & k3_mcart_1(X4,X5,X6) = X3 )
              & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1340])).

fof(f2703,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                | k6_mcart_1(X0,X1,X2,X3) != X5
                | k5_mcart_1(X0,X1,X2,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1341])).

fof(f3732,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
     => ( ( k7_mcart_1(X0,X1,X2,X3) != sK395
          | k6_mcart_1(X0,X1,X2,X3) != sK394
          | k5_mcart_1(X0,X1,X2,X3) != sK393 )
        & k3_mcart_1(sK393,sK394,sK395) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f3731,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                | k6_mcart_1(X0,X1,X2,X3) != X5
                | k5_mcart_1(X0,X1,X2,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ? [X6,X5,X4] :
            ( ( k7_mcart_1(X0,X1,X2,sK392) != X6
              | k6_mcart_1(X0,X1,X2,sK392) != X5
              | k5_mcart_1(X0,X1,X2,sK392) != X4 )
            & k3_mcart_1(X4,X5,X6) = sK392 )
        & m1_subset_1(sK392,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3730,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                  | k6_mcart_1(X0,X1,X2,X3) != X5
                  | k5_mcart_1(X0,X1,X2,X3) != X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ? [X6,X5,X4] :
              ( ( k7_mcart_1(sK389,sK390,sK391,X3) != X6
                | k6_mcart_1(sK389,sK390,sK391,X3) != X5
                | k5_mcart_1(sK389,sK390,sK391,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK389,sK390,sK391)) )
      & k1_xboole_0 != sK391
      & k1_xboole_0 != sK390
      & k1_xboole_0 != sK389 ) ),
    introduced(choice_axiom,[])).

fof(f3733,plain,
    ( ( k7_mcart_1(sK389,sK390,sK391,sK392) != sK395
      | k6_mcart_1(sK389,sK390,sK391,sK392) != sK394
      | k5_mcart_1(sK389,sK390,sK391,sK392) != sK393 )
    & k3_mcart_1(sK393,sK394,sK395) = sK392
    & m1_subset_1(sK392,k3_zfmisc_1(sK389,sK390,sK391))
    & k1_xboole_0 != sK391
    & k1_xboole_0 != sK390
    & k1_xboole_0 != sK389 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK389,sK390,sK391,sK392,sK393,sK394,sK395])],[f2703,f3732,f3731,f3730])).

fof(f6088,plain,(
    m1_subset_1(sK392,k3_zfmisc_1(sK389,sK390,sK391)) ),
    inference(cnf_transformation,[],[f3733])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5939,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6866,plain,(
    m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(sK389,sK390),sK391)) ),
    inference(definition_unfolding,[],[f6088,f5939])).

fof(f6089,plain,(
    k3_mcart_1(sK393,sK394,sK395) = sK392 ),
    inference(cnf_transformation,[],[f3733])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5938,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f6865,plain,(
    k4_tarski(k4_tarski(sK393,sK394),sK395) = sK392 ),
    inference(definition_unfolding,[],[f6089,f5938])).

fof(f1277,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k5_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X5 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2668,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k5_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X5
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1277])).

fof(f3626,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X5
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f2668])).

fof(f3627,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f3626])).

fof(f3628,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X5
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK340(X3,X4) != X4
        & k3_mcart_1(sK340(X3,X4),sK341(X3,X4),sK342(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f3629,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK340(X3,X4) != X4
                    & k3_mcart_1(sK340(X3,X4),sK341(X3,X4),sK342(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK340,sK341,sK342])],[f3627,f3628])).

fof(f5941,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X8
      | k3_mcart_1(X8,X9,X10) != X3
      | k5_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3629])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3749,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6801,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X8
      | k4_tarski(k4_tarski(X8,X9),X10) != X3
      | k5_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f5941,f5938,f5939,f3749,f3749,f3749])).

fof(f7136,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X8
      | k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(k4_tarski(k4_tarski(X8,X9),X10),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f6801])).

fof(f7137,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)) = X8
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)),X0)
      | ~ m1_subset_1(k4_tarski(k4_tarski(X8,X9),X10),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7136])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2671,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f5950,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2671])).

fof(f6808,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f5950,f5939])).

fof(f1278,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( k6_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X6 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2669,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k6_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X6
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1278])).

fof(f3630,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X6
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f2669])).

fof(f3631,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f3630])).

fof(f3632,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X6
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK344(X3,X4) != X4
        & k3_mcart_1(sK343(X3,X4),sK344(X3,X4),sK345(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f3633,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK344(X3,X4) != X4
                    & k3_mcart_1(sK343(X3,X4),sK344(X3,X4),sK345(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK343,sK344,sK345])],[f3631,f3632])).

fof(f5944,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X9
      | k3_mcart_1(X8,X9,X10) != X3
      | k6_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3633])).

fof(f6804,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X9
      | k4_tarski(k4_tarski(X8,X9),X10) != X3
      | k6_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f5944,f5938,f5939,f3749,f3749,f3749])).

fof(f7138,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X9
      | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(k4_tarski(k4_tarski(X8,X9),X10),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f6804])).

fof(f7139,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)) = X9
      | ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)),X1)
      | ~ m1_subset_1(k4_tarski(k4_tarski(X8,X9),X10),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7138])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2672,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f5951,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2672])).

fof(f6809,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f5951,f5939])).

fof(f1279,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ( k7_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X7 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2670,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X7
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1279])).

fof(f3634,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X7
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X7
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f2670])).

fof(f3635,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X7
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f3634])).

fof(f3636,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X7
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK348(X3,X4) != X4
        & k3_mcart_1(sK346(X3,X4),sK347(X3,X4),sK348(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f3637,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK348(X3,X4) != X4
                    & k3_mcart_1(sK346(X3,X4),sK347(X3,X4),sK348(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK346,sK347,sK348])],[f3635,f3636])).

fof(f5947,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X10
      | k3_mcart_1(X8,X9,X10) != X3
      | k7_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3637])).

fof(f6807,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X10
      | k4_tarski(k4_tarski(X8,X9),X10) != X3
      | k7_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f5947,f5938,f5939,f3749,f3749,f3749])).

fof(f7140,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X10
      | k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(k4_tarski(k4_tarski(X8,X9),X10),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f6807])).

fof(f7141,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)) = X10
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X8,X9),X10)),X2)
      | ~ m1_subset_1(k4_tarski(k4_tarski(X8,X9),X10),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7140])).

fof(f1287,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2673,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1287])).

fof(f5952,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2673])).

fof(f6810,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f5952,f5939])).

fof(f6090,plain,
    ( k7_mcart_1(sK389,sK390,sK391,sK392) != sK395
    | k6_mcart_1(sK389,sK390,sK391,sK392) != sK394
    | k5_mcart_1(sK389,sK390,sK391,sK392) != sK393 ),
    inference(cnf_transformation,[],[f3733])).

fof(f6087,plain,(
    k1_xboole_0 != sK391 ),
    inference(cnf_transformation,[],[f3733])).

fof(f6867,plain,(
    o_0_0_xboole_0 != sK391 ),
    inference(definition_unfolding,[],[f6087,f3749])).

fof(f6086,plain,(
    k1_xboole_0 != sK390 ),
    inference(cnf_transformation,[],[f3733])).

fof(f6868,plain,(
    o_0_0_xboole_0 != sK390 ),
    inference(definition_unfolding,[],[f6086,f3749])).

fof(f6085,plain,(
    k1_xboole_0 != sK389 ),
    inference(cnf_transformation,[],[f3733])).

fof(f6869,plain,(
    o_0_0_xboole_0 != sK389 ),
    inference(definition_unfolding,[],[f6085,f3749])).

cnf(c_2327,negated_conjecture,
    ( m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(sK389,sK390),sK391)) ),
    inference(cnf_transformation,[],[f6866])).

cnf(c_66290,plain,
    ( m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(sK389,sK390),sK391)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2327])).

cnf(c_2326,negated_conjecture,
    ( k4_tarski(k4_tarski(sK393,sK394),sK395) = sK392 ),
    inference(cnf_transformation,[],[f6865])).

cnf(c_2183,plain,
    ( ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)),X0)
    | ~ m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X3
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f7137])).

cnf(c_66401,plain,
    ( k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X3
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)),X0) != iProver_top
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2183])).

cnf(c_2190,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f6808])).

cnf(c_66394,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_79443,plain,
    ( k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X3
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_66401,c_66394])).

cnf(c_88127,plain,
    ( k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK393,sK394),sK395)) = sK393
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2326,c_79443])).

cnf(c_88148,plain,
    ( k5_mcart_1(X0,X1,X2,sK392) = sK393
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_88127,c_2326])).

cnf(c_88543,plain,
    ( k5_mcart_1(sK389,sK390,sK391,sK392) = sK393
    | sK391 = o_0_0_xboole_0
    | sK390 = o_0_0_xboole_0
    | sK389 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_66290,c_88148])).

cnf(c_2186,plain,
    ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)),X1)
    | ~ m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f7139])).

cnf(c_66398,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)),X1) != iProver_top
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2186])).

cnf(c_2191,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f6809])).

cnf(c_66393,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2191])).

cnf(c_79431,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_66398,c_66393])).

cnf(c_87237,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK393,sK394),sK395)) = sK394
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2326,c_79431])).

cnf(c_87258,plain,
    ( k6_mcart_1(X0,X1,X2,sK392) = sK394
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_87237,c_2326])).

cnf(c_87343,plain,
    ( k6_mcart_1(sK389,sK390,sK391,sK392) = sK394
    | sK391 = o_0_0_xboole_0
    | sK390 = o_0_0_xboole_0
    | sK389 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_66290,c_87258])).

cnf(c_2189,plain,
    ( ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)),X2)
    | ~ m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f7141])).

cnf(c_66395,plain,
    ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)),X2) != iProver_top
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2189])).

cnf(c_2192,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f6810])).

cnf(c_66392,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2192])).

cnf(c_79419,plain,
    ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_66395,c_66392])).

cnf(c_86535,plain,
    ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK393,sK394),sK395)) = sK395
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2326,c_79419])).

cnf(c_86556,plain,
    ( k7_mcart_1(X0,X1,X2,sK392) = sK395
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK392,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_86535,c_2326])).

cnf(c_86616,plain,
    ( k7_mcart_1(sK389,sK390,sK391,sK392) = sK395
    | sK391 = o_0_0_xboole_0
    | sK390 = o_0_0_xboole_0
    | sK389 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_66290,c_86556])).

cnf(c_2325,negated_conjecture,
    ( k7_mcart_1(sK389,sK390,sK391,sK392) != sK395
    | k6_mcart_1(sK389,sK390,sK391,sK392) != sK394
    | k5_mcart_1(sK389,sK390,sK391,sK392) != sK393 ),
    inference(cnf_transformation,[],[f6090])).

cnf(c_86702,plain,
    ( k6_mcart_1(sK389,sK390,sK391,sK392) != sK394
    | k5_mcart_1(sK389,sK390,sK391,sK392) != sK393
    | sK391 = o_0_0_xboole_0
    | sK390 = o_0_0_xboole_0
    | sK389 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_86616,c_2325])).

cnf(c_87411,plain,
    ( k5_mcart_1(sK389,sK390,sK391,sK392) != sK393
    | sK391 = o_0_0_xboole_0
    | sK390 = o_0_0_xboole_0
    | sK389 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_87343,c_86702])).

cnf(c_88893,plain,
    ( sK391 = o_0_0_xboole_0
    | sK390 = o_0_0_xboole_0
    | sK389 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_88543,c_87411])).

cnf(c_2328,negated_conjecture,
    ( o_0_0_xboole_0 != sK391 ),
    inference(cnf_transformation,[],[f6867])).

cnf(c_88908,plain,
    ( sK390 = o_0_0_xboole_0
    | sK389 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_88893,c_2328])).

cnf(c_2329,negated_conjecture,
    ( o_0_0_xboole_0 != sK390 ),
    inference(cnf_transformation,[],[f6868])).

cnf(c_88929,plain,
    ( sK389 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_88908,c_2329])).

cnf(c_2330,negated_conjecture,
    ( o_0_0_xboole_0 != sK389 ),
    inference(cnf_transformation,[],[f6869])).

cnf(c_89199,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88929,c_2330])).

cnf(c_89200,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_89199])).

%------------------------------------------------------------------------------
