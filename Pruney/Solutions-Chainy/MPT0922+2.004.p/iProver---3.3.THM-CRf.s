%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:25 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  134 (6824 expanded)
%              Number of clauses        :   79 (2317 expanded)
%              Number of leaves         :   14 (1882 expanded)
%              Depth                    :   34
%              Number of atoms          :  720 (52338 expanded)
%              Number of equality atoms :  583 (33706 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X9
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK8 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != sK9
                      | ~ m1_subset_1(X9,sK7) )
                  | ~ m1_subset_1(X8,sK6) )
              | ~ m1_subset_1(X7,sK5) )
          | ~ m1_subset_1(X6,sK4) )
      & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK8 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != sK9
                    | ~ m1_subset_1(X9,sK7) )
                | ~ m1_subset_1(X8,sK6) )
            | ~ m1_subset_1(X7,sK5) )
        | ~ m1_subset_1(X6,sK4) )
    & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f21])).

fof(f40,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f40,f25])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f19,plain,(
    ! [X6,X8,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( X4 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X5
          & m1_subset_1(X9,X3) )
     => ( X4 != X8
        & k4_mcart_1(X6,X7,X8,sK3(X0,X1,X2,X3,X4,X5)) = X5
        & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ? [X9] :
              ( X4 != X8
              & k4_mcart_1(X6,X7,X8,X9) = X5
              & m1_subset_1(X9,X3) )
          & m1_subset_1(X8,X2) )
     => ( ? [X9] :
            ( sK2(X0,X1,X2,X3,X4,X5) != X4
            & k4_mcart_1(X6,X7,sK2(X0,X1,X2,X3,X4,X5),X9) = X5
            & m1_subset_1(X9,X3) )
        & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( ? [X9] :
                  ( X4 != X8
                  & k4_mcart_1(X6,X7,X8,X9) = X5
                  & m1_subset_1(X9,X3) )
              & m1_subset_1(X8,X2) )
          & m1_subset_1(X7,X1) )
     => ( ? [X8] :
            ( ? [X9] :
                ( X4 != X8
                & k4_mcart_1(X6,sK1(X0,X1,X2,X3,X4,X5),X8,X9) = X5
                & m1_subset_1(X9,X3) )
            & m1_subset_1(X8,X2) )
        & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
     => ( ? [X7] :
            ( ? [X8] :
                ( ? [X9] :
                    ( X4 != X8
                    & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5
                    & m1_subset_1(X9,X3) )
                & m1_subset_1(X8,X2) )
            & m1_subset_1(X7,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ( sK2(X0,X1,X2,X3,X4,X5) != X4
        & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5
        & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)
        & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)
        & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)
        & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f19,f18,f17,f16])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5)),sK2(X0,X1,X2,X3,X4,X5)),sK3(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f38,f47,f25])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
                & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
            & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f42,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
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

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f32,f47,f25])).

fof(f65,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f46,plain,(
    k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f33,f47,f25])).

fof(f64,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f34,f25])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f35,f25])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f36,f25])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f37,f25])).

fof(f41,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X9
      | k4_mcart_1(X6,X7,X8,X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X9
      | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(definition_unfolding,[],[f41,f47])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_454,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = X5
    | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X5,X0),sK1(X1,X2,X3,X4,X5,X0)),sK2(X1,X2,X3,X4,X5,X0)),sK3(X1,X2,X3,X4,X5,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_460,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
    | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X5,X4),sK1(X0,X1,X2,X3,X5,X4)),sK2(X0,X1,X2,X3,X5,X4)),sK3(X0,X1,X2,X3,X5,X4)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2869,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_460])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_468,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1236,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_468])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_193,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_216,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_194,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_711,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_712,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_713,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_714,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_715,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_716,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_717,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_718,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1788,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1236,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_2976,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2869,c_1788])).

cnf(c_3660,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2976,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
    | k10_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X2
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_464,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3677,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9)),sK2(sK4,sK5,sK6,sK7,X4,sK9)),sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK2(sK4,sK5,sK6,sK7,X4,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_464])).

cnf(c_4982,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK2(sK4,sK5,sK6,sK7,X0,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_3677])).

cnf(c_4984,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK2(sK4,sK5,sK6,sK7,X0,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4982,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_4989,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(superposition,[status(thm)],[c_3660,c_4984])).

cnf(c_4997,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4989,c_1788])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_469,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1010,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9)
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_469])).

cnf(c_1643,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_14,negated_conjecture,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1646,plain,
    ( k2_mcart_1(sK9) != sK8 ),
    inference(demodulation,[status(thm)],[c_1643,c_14])).

cnf(c_4,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
    | k11_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X3
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_465,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3676,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9)),sK2(sK4,sK5,sK6,sK7,X4,sK9)),sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK3(sK4,sK5,sK6,sK7,X4,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_465])).

cnf(c_4951,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK3(sK4,sK5,sK6,sK7,X0,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_3676])).

cnf(c_4953,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK3(sK4,sK5,sK6,sK7,X0,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4951,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_4958,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(superposition,[status(thm)],[c_3660,c_4953])).

cnf(c_4966,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = k2_mcart_1(sK9)
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4958,c_1643])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | m1_subset_1(sK0(X1,X2,X3,X4,X5,X0),X1)
    | k10_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_456,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2,X3,X5,X4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | m1_subset_1(sK1(X1,X2,X3,X4,X5,X0),X2)
    | k10_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_457,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X3,X5,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | m1_subset_1(sK2(X1,X2,X3,X4,X5,X0),X3)
    | k10_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_458,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2,X3,X5,X4),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | m1_subset_1(sK3(X1,X2,X3,X4,X5,X0),X4)
    | k10_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_459,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2,X3,X5,X4),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ m1_subset_1(X1,sK6)
    | ~ m1_subset_1(X2,sK5)
    | ~ m1_subset_1(X3,sK4)
    | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK9
    | sK8 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_455,plain,
    ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK9
    | sK8 = X3
    | m1_subset_1(X3,sK7) != iProver_top
    | m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3667,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_455])).

cnf(c_3916,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_3667])).

cnf(c_3917,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3916,c_1788])).

cnf(c_21,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4652,plain,
    ( m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3917,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_4653,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4652])).

cnf(c_4663,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_458,c_4653])).

cnf(c_4664,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4663,c_1788])).

cnf(c_4669,plain,
    ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_4670,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4669])).

cnf(c_4679,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_457,c_4670])).

cnf(c_4680,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4679,c_1788])).

cnf(c_4713,plain,
    ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4680,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_4714,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4713])).

cnf(c_4722,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_456,c_4714])).

cnf(c_4723,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4722,c_1788])).

cnf(c_4728,plain,
    ( k2_mcart_1(k1_mcart_1(sK9)) = X0
    | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4723,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718])).

cnf(c_4729,plain,
    ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(renaming,[status(thm)],[c_4728])).

cnf(c_5008,plain,
    ( k2_mcart_1(k1_mcart_1(sK9)) = X0
    | k2_mcart_1(sK9) = sK8 ),
    inference(superposition,[status(thm)],[c_4966,c_4729])).

cnf(c_5049,plain,
    ( k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4997,c_1646,c_5008])).

cnf(c_5279,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_5049,c_5049])).

cnf(c_5730,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_5279,c_18])).

cnf(c_5732,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5730,c_5279])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:00:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/0.99  
% 2.87/0.99  ------  iProver source info
% 2.87/0.99  
% 2.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/0.99  git: non_committed_changes: false
% 2.87/0.99  git: last_make_outside_of_git: false
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options
% 2.87/0.99  
% 2.87/0.99  --out_options                           all
% 2.87/0.99  --tptp_safe_out                         true
% 2.87/0.99  --problem_path                          ""
% 2.87/0.99  --include_path                          ""
% 2.87/0.99  --clausifier                            res/vclausify_rel
% 2.87/0.99  --clausifier_options                    --mode clausify
% 2.87/0.99  --stdin                                 false
% 2.87/0.99  --stats_out                             all
% 2.87/0.99  
% 2.87/0.99  ------ General Options
% 2.87/0.99  
% 2.87/0.99  --fof                                   false
% 2.87/0.99  --time_out_real                         305.
% 2.87/0.99  --time_out_virtual                      -1.
% 2.87/0.99  --symbol_type_check                     false
% 2.87/0.99  --clausify_out                          false
% 2.87/0.99  --sig_cnt_out                           false
% 2.87/0.99  --trig_cnt_out                          false
% 2.87/0.99  --trig_cnt_out_tolerance                1.
% 2.87/0.99  --trig_cnt_out_sk_spl                   false
% 2.87/0.99  --abstr_cl_out                          false
% 2.87/0.99  
% 2.87/0.99  ------ Global Options
% 2.87/0.99  
% 2.87/0.99  --schedule                              default
% 2.87/0.99  --add_important_lit                     false
% 2.87/0.99  --prop_solver_per_cl                    1000
% 2.87/0.99  --min_unsat_core                        false
% 2.87/0.99  --soft_assumptions                      false
% 2.87/0.99  --soft_lemma_size                       3
% 2.87/0.99  --prop_impl_unit_size                   0
% 2.87/0.99  --prop_impl_unit                        []
% 2.87/0.99  --share_sel_clauses                     true
% 2.87/0.99  --reset_solvers                         false
% 2.87/0.99  --bc_imp_inh                            [conj_cone]
% 2.87/0.99  --conj_cone_tolerance                   3.
% 2.87/0.99  --extra_neg_conj                        none
% 2.87/0.99  --large_theory_mode                     true
% 2.87/0.99  --prolific_symb_bound                   200
% 2.87/0.99  --lt_threshold                          2000
% 2.87/0.99  --clause_weak_htbl                      true
% 2.87/0.99  --gc_record_bc_elim                     false
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing Options
% 2.87/0.99  
% 2.87/0.99  --preprocessing_flag                    true
% 2.87/0.99  --time_out_prep_mult                    0.1
% 2.87/0.99  --splitting_mode                        input
% 2.87/0.99  --splitting_grd                         true
% 2.87/0.99  --splitting_cvd                         false
% 2.87/0.99  --splitting_cvd_svl                     false
% 2.87/0.99  --splitting_nvd                         32
% 2.87/0.99  --sub_typing                            true
% 2.87/0.99  --prep_gs_sim                           true
% 2.87/0.99  --prep_unflatten                        true
% 2.87/0.99  --prep_res_sim                          true
% 2.87/0.99  --prep_upred                            true
% 2.87/0.99  --prep_sem_filter                       exhaustive
% 2.87/0.99  --prep_sem_filter_out                   false
% 2.87/0.99  --pred_elim                             true
% 2.87/0.99  --res_sim_input                         true
% 2.87/0.99  --eq_ax_congr_red                       true
% 2.87/0.99  --pure_diseq_elim                       true
% 2.87/0.99  --brand_transform                       false
% 2.87/0.99  --non_eq_to_eq                          false
% 2.87/0.99  --prep_def_merge                        true
% 2.87/0.99  --prep_def_merge_prop_impl              false
% 2.87/0.99  --prep_def_merge_mbd                    true
% 2.87/0.99  --prep_def_merge_tr_red                 false
% 2.87/0.99  --prep_def_merge_tr_cl                  false
% 2.87/0.99  --smt_preprocessing                     true
% 2.87/0.99  --smt_ac_axioms                         fast
% 2.87/0.99  --preprocessed_out                      false
% 2.87/0.99  --preprocessed_stats                    false
% 2.87/0.99  
% 2.87/0.99  ------ Abstraction refinement Options
% 2.87/0.99  
% 2.87/0.99  --abstr_ref                             []
% 2.87/0.99  --abstr_ref_prep                        false
% 2.87/0.99  --abstr_ref_until_sat                   false
% 2.87/0.99  --abstr_ref_sig_restrict                funpre
% 2.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.99  --abstr_ref_under                       []
% 2.87/0.99  
% 2.87/0.99  ------ SAT Options
% 2.87/0.99  
% 2.87/0.99  --sat_mode                              false
% 2.87/0.99  --sat_fm_restart_options                ""
% 2.87/0.99  --sat_gr_def                            false
% 2.87/0.99  --sat_epr_types                         true
% 2.87/0.99  --sat_non_cyclic_types                  false
% 2.87/0.99  --sat_finite_models                     false
% 2.87/0.99  --sat_fm_lemmas                         false
% 2.87/0.99  --sat_fm_prep                           false
% 2.87/0.99  --sat_fm_uc_incr                        true
% 2.87/0.99  --sat_out_model                         small
% 2.87/0.99  --sat_out_clauses                       false
% 2.87/0.99  
% 2.87/0.99  ------ QBF Options
% 2.87/0.99  
% 2.87/0.99  --qbf_mode                              false
% 2.87/0.99  --qbf_elim_univ                         false
% 2.87/0.99  --qbf_dom_inst                          none
% 2.87/0.99  --qbf_dom_pre_inst                      false
% 2.87/0.99  --qbf_sk_in                             false
% 2.87/0.99  --qbf_pred_elim                         true
% 2.87/0.99  --qbf_split                             512
% 2.87/0.99  
% 2.87/0.99  ------ BMC1 Options
% 2.87/0.99  
% 2.87/0.99  --bmc1_incremental                      false
% 2.87/0.99  --bmc1_axioms                           reachable_all
% 2.87/0.99  --bmc1_min_bound                        0
% 2.87/0.99  --bmc1_max_bound                        -1
% 2.87/0.99  --bmc1_max_bound_default                -1
% 2.87/0.99  --bmc1_symbol_reachability              true
% 2.87/0.99  --bmc1_property_lemmas                  false
% 2.87/0.99  --bmc1_k_induction                      false
% 2.87/0.99  --bmc1_non_equiv_states                 false
% 2.87/0.99  --bmc1_deadlock                         false
% 2.87/0.99  --bmc1_ucm                              false
% 2.87/0.99  --bmc1_add_unsat_core                   none
% 2.87/0.99  --bmc1_unsat_core_children              false
% 2.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.99  --bmc1_out_stat                         full
% 2.87/0.99  --bmc1_ground_init                      false
% 2.87/0.99  --bmc1_pre_inst_next_state              false
% 2.87/0.99  --bmc1_pre_inst_state                   false
% 2.87/0.99  --bmc1_pre_inst_reach_state             false
% 2.87/0.99  --bmc1_out_unsat_core                   false
% 2.87/0.99  --bmc1_aig_witness_out                  false
% 2.87/0.99  --bmc1_verbose                          false
% 2.87/0.99  --bmc1_dump_clauses_tptp                false
% 2.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.99  --bmc1_dump_file                        -
% 2.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.99  --bmc1_ucm_extend_mode                  1
% 2.87/0.99  --bmc1_ucm_init_mode                    2
% 2.87/0.99  --bmc1_ucm_cone_mode                    none
% 2.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.99  --bmc1_ucm_relax_model                  4
% 2.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.99  --bmc1_ucm_layered_model                none
% 2.87/0.99  --bmc1_ucm_max_lemma_size               10
% 2.87/0.99  
% 2.87/0.99  ------ AIG Options
% 2.87/0.99  
% 2.87/0.99  --aig_mode                              false
% 2.87/0.99  
% 2.87/0.99  ------ Instantiation Options
% 2.87/0.99  
% 2.87/0.99  --instantiation_flag                    true
% 2.87/0.99  --inst_sos_flag                         false
% 2.87/0.99  --inst_sos_phase                        true
% 2.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel_side                     num_symb
% 2.87/0.99  --inst_solver_per_active                1400
% 2.87/0.99  --inst_solver_calls_frac                1.
% 2.87/0.99  --inst_passive_queue_type               priority_queues
% 2.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.99  --inst_passive_queues_freq              [25;2]
% 2.87/0.99  --inst_dismatching                      true
% 2.87/0.99  --inst_eager_unprocessed_to_passive     true
% 2.87/0.99  --inst_prop_sim_given                   true
% 2.87/0.99  --inst_prop_sim_new                     false
% 2.87/0.99  --inst_subs_new                         false
% 2.87/0.99  --inst_eq_res_simp                      false
% 2.87/0.99  --inst_subs_given                       false
% 2.87/0.99  --inst_orphan_elimination               true
% 2.87/0.99  --inst_learning_loop_flag               true
% 2.87/0.99  --inst_learning_start                   3000
% 2.87/0.99  --inst_learning_factor                  2
% 2.87/0.99  --inst_start_prop_sim_after_learn       3
% 2.87/0.99  --inst_sel_renew                        solver
% 2.87/0.99  --inst_lit_activity_flag                true
% 2.87/0.99  --inst_restr_to_given                   false
% 2.87/0.99  --inst_activity_threshold               500
% 2.87/0.99  --inst_out_proof                        true
% 2.87/0.99  
% 2.87/0.99  ------ Resolution Options
% 2.87/0.99  
% 2.87/0.99  --resolution_flag                       true
% 2.87/0.99  --res_lit_sel                           adaptive
% 2.87/0.99  --res_lit_sel_side                      none
% 2.87/0.99  --res_ordering                          kbo
% 2.87/0.99  --res_to_prop_solver                    active
% 2.87/0.99  --res_prop_simpl_new                    false
% 2.87/0.99  --res_prop_simpl_given                  true
% 2.87/0.99  --res_passive_queue_type                priority_queues
% 2.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.99  --res_passive_queues_freq               [15;5]
% 2.87/0.99  --res_forward_subs                      full
% 2.87/0.99  --res_backward_subs                     full
% 2.87/0.99  --res_forward_subs_resolution           true
% 2.87/0.99  --res_backward_subs_resolution          true
% 2.87/0.99  --res_orphan_elimination                true
% 2.87/0.99  --res_time_limit                        2.
% 2.87/0.99  --res_out_proof                         true
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Options
% 2.87/0.99  
% 2.87/0.99  --superposition_flag                    true
% 2.87/0.99  --sup_passive_queue_type                priority_queues
% 2.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.99  --demod_completeness_check              fast
% 2.87/0.99  --demod_use_ground                      true
% 2.87/0.99  --sup_to_prop_solver                    passive
% 2.87/0.99  --sup_prop_simpl_new                    true
% 2.87/0.99  --sup_prop_simpl_given                  true
% 2.87/0.99  --sup_fun_splitting                     false
% 2.87/0.99  --sup_smt_interval                      50000
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Simplification Setup
% 2.87/0.99  
% 2.87/0.99  --sup_indices_passive                   []
% 2.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_full_bw                           [BwDemod]
% 2.87/0.99  --sup_immed_triv                        [TrivRules]
% 2.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_immed_bw_main                     []
% 2.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  
% 2.87/0.99  ------ Combination Options
% 2.87/0.99  
% 2.87/0.99  --comb_res_mult                         3
% 2.87/0.99  --comb_sup_mult                         2
% 2.87/0.99  --comb_inst_mult                        10
% 2.87/0.99  
% 2.87/0.99  ------ Debug Options
% 2.87/0.99  
% 2.87/0.99  --dbg_backtrace                         false
% 2.87/0.99  --dbg_dump_prop_clauses                 false
% 2.87/0.99  --dbg_dump_prop_clauses_file            -
% 2.87/0.99  --dbg_out_stat                          false
% 2.87/0.99  ------ Parsing...
% 2.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/0.99  ------ Proving...
% 2.87/0.99  ------ Problem Properties 
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  clauses                                 21
% 2.87/0.99  conjectures                             7
% 2.87/0.99  EPR                                     4
% 2.87/0.99  Horn                                    7
% 2.87/0.99  unary                                   6
% 2.87/0.99  binary                                  0
% 2.87/0.99  lits                                    102
% 2.87/0.99  lits eq                                 79
% 2.87/0.99  fd_pure                                 0
% 2.87/0.99  fd_pseudo                               0
% 2.87/0.99  fd_cond                                 5
% 2.87/0.99  fd_pseudo_cond                          5
% 2.87/0.99  AC symbols                              0
% 2.87/0.99  
% 2.87/0.99  ------ Schedule dynamic 5 is on 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  Current options:
% 2.87/0.99  ------ 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options
% 2.87/0.99  
% 2.87/0.99  --out_options                           all
% 2.87/0.99  --tptp_safe_out                         true
% 2.87/0.99  --problem_path                          ""
% 2.87/0.99  --include_path                          ""
% 2.87/0.99  --clausifier                            res/vclausify_rel
% 2.87/0.99  --clausifier_options                    --mode clausify
% 2.87/0.99  --stdin                                 false
% 2.87/0.99  --stats_out                             all
% 2.87/0.99  
% 2.87/0.99  ------ General Options
% 2.87/0.99  
% 2.87/0.99  --fof                                   false
% 2.87/0.99  --time_out_real                         305.
% 2.87/0.99  --time_out_virtual                      -1.
% 2.87/0.99  --symbol_type_check                     false
% 2.87/0.99  --clausify_out                          false
% 2.87/0.99  --sig_cnt_out                           false
% 2.87/0.99  --trig_cnt_out                          false
% 2.87/0.99  --trig_cnt_out_tolerance                1.
% 2.87/0.99  --trig_cnt_out_sk_spl                   false
% 2.87/0.99  --abstr_cl_out                          false
% 2.87/0.99  
% 2.87/0.99  ------ Global Options
% 2.87/0.99  
% 2.87/0.99  --schedule                              default
% 2.87/0.99  --add_important_lit                     false
% 2.87/0.99  --prop_solver_per_cl                    1000
% 2.87/0.99  --min_unsat_core                        false
% 2.87/0.99  --soft_assumptions                      false
% 2.87/0.99  --soft_lemma_size                       3
% 2.87/0.99  --prop_impl_unit_size                   0
% 2.87/0.99  --prop_impl_unit                        []
% 2.87/0.99  --share_sel_clauses                     true
% 2.87/0.99  --reset_solvers                         false
% 2.87/0.99  --bc_imp_inh                            [conj_cone]
% 2.87/0.99  --conj_cone_tolerance                   3.
% 2.87/0.99  --extra_neg_conj                        none
% 2.87/0.99  --large_theory_mode                     true
% 2.87/0.99  --prolific_symb_bound                   200
% 2.87/0.99  --lt_threshold                          2000
% 2.87/0.99  --clause_weak_htbl                      true
% 2.87/0.99  --gc_record_bc_elim                     false
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing Options
% 2.87/0.99  
% 2.87/0.99  --preprocessing_flag                    true
% 2.87/0.99  --time_out_prep_mult                    0.1
% 2.87/0.99  --splitting_mode                        input
% 2.87/0.99  --splitting_grd                         true
% 2.87/0.99  --splitting_cvd                         false
% 2.87/0.99  --splitting_cvd_svl                     false
% 2.87/0.99  --splitting_nvd                         32
% 2.87/0.99  --sub_typing                            true
% 2.87/0.99  --prep_gs_sim                           true
% 2.87/0.99  --prep_unflatten                        true
% 2.87/0.99  --prep_res_sim                          true
% 2.87/0.99  --prep_upred                            true
% 2.87/0.99  --prep_sem_filter                       exhaustive
% 2.87/0.99  --prep_sem_filter_out                   false
% 2.87/0.99  --pred_elim                             true
% 2.87/0.99  --res_sim_input                         true
% 2.87/0.99  --eq_ax_congr_red                       true
% 2.87/0.99  --pure_diseq_elim                       true
% 2.87/0.99  --brand_transform                       false
% 2.87/0.99  --non_eq_to_eq                          false
% 2.87/0.99  --prep_def_merge                        true
% 2.87/0.99  --prep_def_merge_prop_impl              false
% 2.87/0.99  --prep_def_merge_mbd                    true
% 2.87/0.99  --prep_def_merge_tr_red                 false
% 2.87/0.99  --prep_def_merge_tr_cl                  false
% 2.87/0.99  --smt_preprocessing                     true
% 2.87/0.99  --smt_ac_axioms                         fast
% 2.87/0.99  --preprocessed_out                      false
% 2.87/0.99  --preprocessed_stats                    false
% 2.87/0.99  
% 2.87/0.99  ------ Abstraction refinement Options
% 2.87/0.99  
% 2.87/0.99  --abstr_ref                             []
% 2.87/0.99  --abstr_ref_prep                        false
% 2.87/0.99  --abstr_ref_until_sat                   false
% 2.87/0.99  --abstr_ref_sig_restrict                funpre
% 2.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.99  --abstr_ref_under                       []
% 2.87/0.99  
% 2.87/0.99  ------ SAT Options
% 2.87/0.99  
% 2.87/0.99  --sat_mode                              false
% 2.87/0.99  --sat_fm_restart_options                ""
% 2.87/0.99  --sat_gr_def                            false
% 2.87/0.99  --sat_epr_types                         true
% 2.87/0.99  --sat_non_cyclic_types                  false
% 2.87/0.99  --sat_finite_models                     false
% 2.87/0.99  --sat_fm_lemmas                         false
% 2.87/0.99  --sat_fm_prep                           false
% 2.87/0.99  --sat_fm_uc_incr                        true
% 2.87/0.99  --sat_out_model                         small
% 2.87/0.99  --sat_out_clauses                       false
% 2.87/0.99  
% 2.87/0.99  ------ QBF Options
% 2.87/0.99  
% 2.87/0.99  --qbf_mode                              false
% 2.87/0.99  --qbf_elim_univ                         false
% 2.87/0.99  --qbf_dom_inst                          none
% 2.87/0.99  --qbf_dom_pre_inst                      false
% 2.87/0.99  --qbf_sk_in                             false
% 2.87/0.99  --qbf_pred_elim                         true
% 2.87/0.99  --qbf_split                             512
% 2.87/0.99  
% 2.87/0.99  ------ BMC1 Options
% 2.87/0.99  
% 2.87/0.99  --bmc1_incremental                      false
% 2.87/0.99  --bmc1_axioms                           reachable_all
% 2.87/0.99  --bmc1_min_bound                        0
% 2.87/0.99  --bmc1_max_bound                        -1
% 2.87/0.99  --bmc1_max_bound_default                -1
% 2.87/0.99  --bmc1_symbol_reachability              true
% 2.87/0.99  --bmc1_property_lemmas                  false
% 2.87/0.99  --bmc1_k_induction                      false
% 2.87/0.99  --bmc1_non_equiv_states                 false
% 2.87/0.99  --bmc1_deadlock                         false
% 2.87/0.99  --bmc1_ucm                              false
% 2.87/0.99  --bmc1_add_unsat_core                   none
% 2.87/0.99  --bmc1_unsat_core_children              false
% 2.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.99  --bmc1_out_stat                         full
% 2.87/0.99  --bmc1_ground_init                      false
% 2.87/0.99  --bmc1_pre_inst_next_state              false
% 2.87/0.99  --bmc1_pre_inst_state                   false
% 2.87/0.99  --bmc1_pre_inst_reach_state             false
% 2.87/0.99  --bmc1_out_unsat_core                   false
% 2.87/0.99  --bmc1_aig_witness_out                  false
% 2.87/0.99  --bmc1_verbose                          false
% 2.87/0.99  --bmc1_dump_clauses_tptp                false
% 2.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.99  --bmc1_dump_file                        -
% 2.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.99  --bmc1_ucm_extend_mode                  1
% 2.87/0.99  --bmc1_ucm_init_mode                    2
% 2.87/0.99  --bmc1_ucm_cone_mode                    none
% 2.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.99  --bmc1_ucm_relax_model                  4
% 2.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.99  --bmc1_ucm_layered_model                none
% 2.87/0.99  --bmc1_ucm_max_lemma_size               10
% 2.87/0.99  
% 2.87/0.99  ------ AIG Options
% 2.87/0.99  
% 2.87/0.99  --aig_mode                              false
% 2.87/0.99  
% 2.87/0.99  ------ Instantiation Options
% 2.87/0.99  
% 2.87/0.99  --instantiation_flag                    true
% 2.87/0.99  --inst_sos_flag                         false
% 2.87/0.99  --inst_sos_phase                        true
% 2.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel_side                     none
% 2.87/0.99  --inst_solver_per_active                1400
% 2.87/0.99  --inst_solver_calls_frac                1.
% 2.87/0.99  --inst_passive_queue_type               priority_queues
% 2.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.99  --inst_passive_queues_freq              [25;2]
% 2.87/0.99  --inst_dismatching                      true
% 2.87/0.99  --inst_eager_unprocessed_to_passive     true
% 2.87/0.99  --inst_prop_sim_given                   true
% 2.87/0.99  --inst_prop_sim_new                     false
% 2.87/0.99  --inst_subs_new                         false
% 2.87/0.99  --inst_eq_res_simp                      false
% 2.87/0.99  --inst_subs_given                       false
% 2.87/0.99  --inst_orphan_elimination               true
% 2.87/0.99  --inst_learning_loop_flag               true
% 2.87/0.99  --inst_learning_start                   3000
% 2.87/0.99  --inst_learning_factor                  2
% 2.87/0.99  --inst_start_prop_sim_after_learn       3
% 2.87/0.99  --inst_sel_renew                        solver
% 2.87/0.99  --inst_lit_activity_flag                true
% 2.87/0.99  --inst_restr_to_given                   false
% 2.87/0.99  --inst_activity_threshold               500
% 2.87/0.99  --inst_out_proof                        true
% 2.87/0.99  
% 2.87/0.99  ------ Resolution Options
% 2.87/0.99  
% 2.87/0.99  --resolution_flag                       false
% 2.87/0.99  --res_lit_sel                           adaptive
% 2.87/0.99  --res_lit_sel_side                      none
% 2.87/0.99  --res_ordering                          kbo
% 2.87/0.99  --res_to_prop_solver                    active
% 2.87/0.99  --res_prop_simpl_new                    false
% 2.87/0.99  --res_prop_simpl_given                  true
% 2.87/0.99  --res_passive_queue_type                priority_queues
% 2.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.99  --res_passive_queues_freq               [15;5]
% 2.87/0.99  --res_forward_subs                      full
% 2.87/0.99  --res_backward_subs                     full
% 2.87/0.99  --res_forward_subs_resolution           true
% 2.87/0.99  --res_backward_subs_resolution          true
% 2.87/0.99  --res_orphan_elimination                true
% 2.87/0.99  --res_time_limit                        2.
% 2.87/0.99  --res_out_proof                         true
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Options
% 2.87/0.99  
% 2.87/0.99  --superposition_flag                    true
% 2.87/0.99  --sup_passive_queue_type                priority_queues
% 2.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.99  --demod_completeness_check              fast
% 2.87/0.99  --demod_use_ground                      true
% 2.87/0.99  --sup_to_prop_solver                    passive
% 2.87/0.99  --sup_prop_simpl_new                    true
% 2.87/0.99  --sup_prop_simpl_given                  true
% 2.87/0.99  --sup_fun_splitting                     false
% 2.87/0.99  --sup_smt_interval                      50000
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Simplification Setup
% 2.87/0.99  
% 2.87/0.99  --sup_indices_passive                   []
% 2.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_full_bw                           [BwDemod]
% 2.87/0.99  --sup_immed_triv                        [TrivRules]
% 2.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_immed_bw_main                     []
% 2.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  
% 2.87/0.99  ------ Combination Options
% 2.87/0.99  
% 2.87/0.99  --comb_res_mult                         3
% 2.87/0.99  --comb_sup_mult                         2
% 2.87/0.99  --comb_inst_mult                        10
% 2.87/0.99  
% 2.87/0.99  ------ Debug Options
% 2.87/0.99  
% 2.87/0.99  --dbg_backtrace                         false
% 2.87/0.99  --dbg_dump_prop_clauses                 false
% 2.87/0.99  --dbg_dump_prop_clauses_file            -
% 2.87/0.99  --dbg_out_stat                          false
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ Proving...
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  % SZS status Theorem for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99   Resolution empty clause
% 2.87/0.99  
% 2.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  fof(f7,conjecture,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f8,negated_conjecture,(
% 2.87/0.99    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.87/0.99    inference(negated_conjecture,[],[f7])).
% 2.87/0.99  
% 2.87/0.99  fof(f14,plain,(
% 2.87/0.99    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.87/0.99    inference(ennf_transformation,[],[f8])).
% 2.87/0.99  
% 2.87/0.99  fof(f15,plain,(
% 2.87/0.99    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.87/0.99    inference(flattening,[],[f14])).
% 2.87/0.99  
% 2.87/0.99  fof(f21,plain,(
% 2.87/0.99    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f22,plain,(
% 2.87/0.99    k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f21])).
% 2.87/0.99  
% 2.87/0.99  fof(f40,plain,(
% 2.87/0.99    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f3,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f25,plain,(
% 2.87/0.99    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f3])).
% 2.87/0.99  
% 2.87/0.99  fof(f63,plain,(
% 2.87/0.99    m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7))),
% 2.87/0.99    inference(definition_unfolding,[],[f40,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f6,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f12,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.87/0.99    inference(ennf_transformation,[],[f6])).
% 2.87/0.99  
% 2.87/0.99  fof(f13,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.87/0.99    inference(flattening,[],[f12])).
% 2.87/0.99  
% 2.87/0.99  fof(f19,plain,(
% 2.87/0.99    ( ! [X6,X8,X7] : (! [X5,X4,X3,X2,X1,X0] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) => (X4 != X8 & k4_mcart_1(X6,X7,X8,sK3(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)))) )),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f18,plain,(
% 2.87/0.99    ( ! [X6,X7] : (! [X5,X4,X3,X2,X1,X0] : (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) => (? [X9] : (sK2(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(X6,X7,sK2(X0,X1,X2,X3,X4,X5),X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)))) )),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f17,plain,(
% 2.87/0.99    ( ! [X6] : (! [X5,X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) => (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,sK1(X0,X1,X2,X3,X4,X5),X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)))) )),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f16,plain,(
% 2.87/0.99    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) => (? [X7] : (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f20,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ((((sK2(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f19,f18,f17,f16])).
% 2.87/0.99  
% 2.87/0.99  fof(f38,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f2,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f24,plain,(
% 2.87/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f2])).
% 2.87/0.99  
% 2.87/0.99  fof(f1,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f23,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f1])).
% 2.87/0.99  
% 2.87/0.99  fof(f47,plain,(
% 2.87/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 2.87/0.99    inference(definition_unfolding,[],[f24,f23])).
% 2.87/0.99  
% 2.87/0.99  fof(f57,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5)),sK2(X0,X1,X2,X3,X4,X5)),sK3(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(definition_unfolding,[],[f38,f47,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f4,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f9,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.87/0.99    inference(ennf_transformation,[],[f4])).
% 2.87/0.99  
% 2.87/0.99  fof(f28,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.87/0.99    inference(cnf_transformation,[],[f9])).
% 2.87/0.99  
% 2.87/0.99  fof(f49,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.87/0.99    inference(definition_unfolding,[],[f28,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f42,plain,(
% 2.87/0.99    k1_xboole_0 != sK4),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f43,plain,(
% 2.87/0.99    k1_xboole_0 != sK5),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f44,plain,(
% 2.87/0.99    k1_xboole_0 != sK6),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f45,plain,(
% 2.87/0.99    k1_xboole_0 != sK7),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f5,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f10,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.87/0.99    inference(ennf_transformation,[],[f5])).
% 2.87/0.99  
% 2.87/0.99  fof(f11,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.87/0.99    inference(flattening,[],[f10])).
% 2.87/0.99  
% 2.87/0.99  fof(f32,plain,(
% 2.87/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f11])).
% 2.87/0.99  
% 2.87/0.99  fof(f53,plain,(
% 2.87/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(definition_unfolding,[],[f32,f47,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f65,plain,(
% 2.87/0.99    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(equality_resolution,[],[f53])).
% 2.87/0.99  
% 2.87/0.99  fof(f29,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.87/0.99    inference(cnf_transformation,[],[f9])).
% 2.87/0.99  
% 2.87/0.99  fof(f48,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.87/0.99    inference(definition_unfolding,[],[f29,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f46,plain,(
% 2.87/0.99    k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f33,plain,(
% 2.87/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f11])).
% 2.87/0.99  
% 2.87/0.99  fof(f52,plain,(
% 2.87/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(definition_unfolding,[],[f33,f47,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f64,plain,(
% 2.87/0.99    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(equality_resolution,[],[f52])).
% 2.87/0.99  
% 2.87/0.99  fof(f34,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f61,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(definition_unfolding,[],[f34,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f35,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f60,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(definition_unfolding,[],[f35,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f36,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f59,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(definition_unfolding,[],[f36,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f37,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f58,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 2.87/0.99    inference(definition_unfolding,[],[f37,f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f41,plain,(
% 2.87/0.99    ( ! [X6,X8,X7,X9] : (sK8 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f62,plain,(
% 2.87/0.99    ( ! [X6,X8,X7,X9] : (sK8 = X9 | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 2.87/0.99    inference(definition_unfolding,[],[f41,f47])).
% 2.87/0.99  
% 2.87/0.99  cnf(c_20,negated_conjecture,
% 2.87/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) ),
% 2.87/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_454,plain,
% 2.87/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_9,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.87/0.99      | k10_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.87/0.99      | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X5,X0),sK1(X1,X2,X3,X4,X5,X0)),sK2(X1,X2,X3,X4,X5,X0)),sK3(X1,X2,X3,X4,X5,X0)) = X0
% 2.87/1.00      | k1_xboole_0 = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_460,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.87/1.00      | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X5,X4),sK1(X0,X1,X2,X3,X5,X4)),sK2(X0,X1,X2,X3,X5,X4)),sK3(X0,X1,X2,X3,X5,X4)) = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2869,plain,
% 2.87/1.00      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.87/1.00      | k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_454,c_460]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.87/1.00      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.87/1.00      | k1_xboole_0 = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_468,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1236,plain,
% 2.87/1.00      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9))
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_454,c_468]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_18,negated_conjecture,
% 2.87/1.00      ( k1_xboole_0 != sK4 ),
% 2.87/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_17,negated_conjecture,
% 2.87/1.00      ( k1_xboole_0 != sK5 ),
% 2.87/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_16,negated_conjecture,
% 2.87/1.00      ( k1_xboole_0 != sK6 ),
% 2.87/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_15,negated_conjecture,
% 2.87/1.00      ( k1_xboole_0 != sK7 ),
% 2.87/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_193,plain,( X0 = X0 ),theory(equality) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_216,plain,
% 2.87/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_194,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_711,plain,
% 2.87/1.00      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_194]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_712,plain,
% 2.87/1.00      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_711]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_713,plain,
% 2.87/1.00      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_194]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_714,plain,
% 2.87/1.00      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_713]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_715,plain,
% 2.87/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_194]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_716,plain,
% 2.87/1.00      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_715]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_717,plain,
% 2.87/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_194]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_718,plain,
% 2.87/1.00      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_717]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1788,plain,
% 2.87/1.00      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9)) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_1236,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2976,plain,
% 2.87/1.00      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0 ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2869,c_1788]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3660,plain,
% 2.87/1.00      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2976,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5,plain,
% 2.87/1.00      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
% 2.87/1.00      | k10_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X2
% 2.87/1.00      | k1_xboole_0 = X7
% 2.87/1.00      | k1_xboole_0 = X6
% 2.87/1.00      | k1_xboole_0 = X5
% 2.87/1.00      | k1_xboole_0 = X4 ),
% 2.87/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_464,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3677,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9)),sK2(sK4,sK5,sK6,sK7,X4,sK9)),sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK2(sK4,sK5,sK6,sK7,X4,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_3660,c_464]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4982,plain,
% 2.87/1.00      ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK2(sK4,sK5,sK6,sK7,X0,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_454,c_3677]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4984,plain,
% 2.87/1.00      ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK2(sK4,sK5,sK6,sK7,X0,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_4982,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4989,plain,
% 2.87/1.00      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_3660,c_4984]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4997,plain,
% 2.87/1.00      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = k2_mcart_1(k1_mcart_1(sK9))
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_4989,c_1788]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_0,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.87/1.00      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 2.87/1.00      | k1_xboole_0 = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_469,plain,
% 2.87/1.00      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1010,plain,
% 2.87/1.00      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9)
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_454,c_469]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1643,plain,
% 2.87/1.00      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_1010,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_14,negated_conjecture,
% 2.87/1.00      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
% 2.87/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1646,plain,
% 2.87/1.00      ( k2_mcart_1(sK9) != sK8 ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_1643,c_14]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4,plain,
% 2.87/1.00      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
% 2.87/1.00      | k11_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X3
% 2.87/1.00      | k1_xboole_0 = X7
% 2.87/1.00      | k1_xboole_0 = X6
% 2.87/1.00      | k1_xboole_0 = X5
% 2.87/1.00      | k1_xboole_0 = X4 ),
% 2.87/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_465,plain,
% 2.87/1.00      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3676,plain,
% 2.87/1.00      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9)),sK2(sK4,sK5,sK6,sK7,X4,sK9)),sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK3(sK4,sK5,sK6,sK7,X4,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_3660,c_465]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4951,plain,
% 2.87/1.00      ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK3(sK4,sK5,sK6,sK7,X0,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_454,c_3676]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4953,plain,
% 2.87/1.00      ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK3(sK4,sK5,sK6,sK7,X0,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_4951,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4958,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_3660,c_4953]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4966,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = k2_mcart_1(sK9)
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_4958,c_1643]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_13,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.87/1.00      | m1_subset_1(sK0(X1,X2,X3,X4,X5,X0),X1)
% 2.87/1.00      | k10_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.87/1.00      | k1_xboole_0 = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_456,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(X0,X1,X2,X3,X5,X4),X0) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_12,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.87/1.00      | m1_subset_1(sK1(X1,X2,X3,X4,X5,X0),X2)
% 2.87/1.00      | k10_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.87/1.00      | k1_xboole_0 = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_457,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
% 2.87/1.00      | m1_subset_1(sK1(X0,X1,X2,X3,X5,X4),X1) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_11,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.87/1.00      | m1_subset_1(sK2(X1,X2,X3,X4,X5,X0),X3)
% 2.87/1.00      | k10_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.87/1.00      | k1_xboole_0 = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_458,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2(X0,X1,X2,X3,X5,X4),X2) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_10,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.87/1.00      | m1_subset_1(sK3(X1,X2,X3,X4,X5,X0),X4)
% 2.87/1.00      | k10_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.87/1.00      | k1_xboole_0 = X4
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_459,plain,
% 2.87/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.87/1.00      | k1_xboole_0 = X3
% 2.87/1.00      | k1_xboole_0 = X2
% 2.87/1.00      | k1_xboole_0 = X1
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top
% 2.87/1.00      | m1_subset_1(sK3(X0,X1,X2,X3,X5,X4),X3) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_19,negated_conjecture,
% 2.87/1.00      ( ~ m1_subset_1(X0,sK7)
% 2.87/1.00      | ~ m1_subset_1(X1,sK6)
% 2.87/1.00      | ~ m1_subset_1(X2,sK5)
% 2.87/1.00      | ~ m1_subset_1(X3,sK4)
% 2.87/1.00      | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK9
% 2.87/1.00      | sK8 = X0 ),
% 2.87/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_455,plain,
% 2.87/1.00      ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK9
% 2.87/1.00      | sK8 = X3
% 2.87/1.00      | m1_subset_1(X3,sK7) != iProver_top
% 2.87/1.00      | m1_subset_1(X2,sK6) != iProver_top
% 2.87/1.00      | m1_subset_1(X1,sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(X0,sK4) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3667,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) != iProver_top
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_3660,c_455]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3916,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_459,c_3667]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3917,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_3916,c_1788]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_21,plain,
% 2.87/1.00      ( m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4652,plain,
% 2.87/1.00      ( m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_3917,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4653,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_4652]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4663,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_458,c_4653]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4664,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_4663,c_1788]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4669,plain,
% 2.87/1.00      ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_4664,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4670,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_4669]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4679,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_457,c_4670]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4680,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_4679,c_1788]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4713,plain,
% 2.87/1.00      ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_4680,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4714,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_4713]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4722,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_456,c_4714]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4723,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.87/1.00      | k2_mcart_1(k1_mcart_1(sK9)) = X0
% 2.87/1.00      | sK7 = k1_xboole_0
% 2.87/1.00      | sK6 = k1_xboole_0
% 2.87/1.00      | sK5 = k1_xboole_0
% 2.87/1.00      | sK4 = k1_xboole_0
% 2.87/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_4722,c_1788]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4728,plain,
% 2.87/1.00      ( k2_mcart_1(k1_mcart_1(sK9)) = X0 | sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_4723,c_21,c_18,c_17,c_16,c_15,c_216,c_712,c_714,c_716,c_718]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4729,plain,
% 2.87/1.00      ( sK3(sK4,sK5,sK6,sK7,X0,sK9) = sK8 | k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_4728]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5008,plain,
% 2.87/1.00      ( k2_mcart_1(k1_mcart_1(sK9)) = X0 | k2_mcart_1(sK9) = sK8 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_4966,c_4729]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5049,plain,
% 2.87/1.00      ( k2_mcart_1(k1_mcart_1(sK9)) = X0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_4997,c_1646,c_5008]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5279,plain,
% 2.87/1.00      ( X0 = X1 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_5049,c_5049]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5730,plain,
% 2.87/1.00      ( k1_xboole_0 != X0 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_5279,c_18]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5732,plain,
% 2.87/1.00      ( $false ),
% 2.87/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5730,c_5279]) ).
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.00  
% 2.87/1.00  ------                               Statistics
% 2.87/1.00  
% 2.87/1.00  ------ General
% 2.87/1.00  
% 2.87/1.00  abstr_ref_over_cycles:                  0
% 2.87/1.00  abstr_ref_under_cycles:                 0
% 2.87/1.00  gc_basic_clause_elim:                   0
% 2.87/1.00  forced_gc_time:                         0
% 2.87/1.00  parsing_time:                           0.01
% 2.87/1.00  unif_index_cands_time:                  0.
% 2.87/1.00  unif_index_add_time:                    0.
% 2.87/1.00  orderings_time:                         0.
% 2.87/1.00  out_proof_time:                         0.012
% 2.87/1.00  total_time:                             0.233
% 2.87/1.00  num_of_symbols:                         52
% 2.87/1.00  num_of_terms:                           11406
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing
% 2.87/1.00  
% 2.87/1.00  num_of_splits:                          0
% 2.87/1.00  num_of_split_atoms:                     0
% 2.87/1.00  num_of_reused_defs:                     0
% 2.87/1.00  num_eq_ax_congr_red:                    72
% 2.87/1.00  num_of_sem_filtered_clauses:            1
% 2.87/1.00  num_of_subtypes:                        0
% 2.87/1.00  monotx_restored_types:                  0
% 2.87/1.00  sat_num_of_epr_types:                   0
% 2.87/1.00  sat_num_of_non_cyclic_types:            0
% 2.87/1.00  sat_guarded_non_collapsed_types:        0
% 2.87/1.00  num_pure_diseq_elim:                    0
% 2.87/1.00  simp_replaced_by:                       0
% 2.87/1.00  res_preprocessed:                       88
% 2.87/1.00  prep_upred:                             0
% 2.87/1.00  prep_unflattend:                        0
% 2.87/1.00  smt_new_axioms:                         0
% 2.87/1.00  pred_elim_cands:                        1
% 2.87/1.00  pred_elim:                              0
% 2.87/1.00  pred_elim_cl:                           0
% 2.87/1.00  pred_elim_cycles:                       1
% 2.87/1.00  merged_defs:                            0
% 2.87/1.00  merged_defs_ncl:                        0
% 2.87/1.00  bin_hyper_res:                          0
% 2.87/1.00  prep_cycles:                            3
% 2.87/1.00  pred_elim_time:                         0.
% 2.87/1.00  splitting_time:                         0.
% 2.87/1.00  sem_filter_time:                        0.
% 2.87/1.00  monotx_time:                            0.
% 2.87/1.00  subtype_inf_time:                       0.
% 2.87/1.00  
% 2.87/1.00  ------ Problem properties
% 2.87/1.00  
% 2.87/1.00  clauses:                                21
% 2.87/1.00  conjectures:                            7
% 2.87/1.00  epr:                                    4
% 2.87/1.00  horn:                                   7
% 2.87/1.00  ground:                                 6
% 2.87/1.00  unary:                                  6
% 2.87/1.00  binary:                                 0
% 2.87/1.00  lits:                                   102
% 2.87/1.00  lits_eq:                                79
% 2.87/1.00  fd_pure:                                0
% 2.87/1.00  fd_pseudo:                              0
% 2.87/1.00  fd_cond:                                5
% 2.87/1.00  fd_pseudo_cond:                         5
% 2.87/1.00  ac_symbols:                             0
% 2.87/1.00  
% 2.87/1.00  ------ Propositional Solver
% 2.87/1.00  
% 2.87/1.00  prop_solver_calls:                      22
% 2.87/1.00  prop_fast_solver_calls:                 1159
% 2.87/1.00  smt_solver_calls:                       0
% 2.87/1.00  smt_fast_solver_calls:                  0
% 2.87/1.00  prop_num_of_clauses:                    2081
% 2.87/1.00  prop_preprocess_simplified:             7515
% 2.87/1.00  prop_fo_subsumed:                       53
% 2.87/1.00  prop_solver_time:                       0.
% 2.87/1.00  smt_solver_time:                        0.
% 2.87/1.00  smt_fast_solver_time:                   0.
% 2.87/1.00  prop_fast_solver_time:                  0.
% 2.87/1.00  prop_unsat_core_time:                   0.
% 2.87/1.00  
% 2.87/1.00  ------ QBF
% 2.87/1.00  
% 2.87/1.00  qbf_q_res:                              0
% 2.87/1.00  qbf_num_tautologies:                    0
% 2.87/1.00  qbf_prep_cycles:                        0
% 2.87/1.00  
% 2.87/1.00  ------ BMC1
% 2.87/1.00  
% 2.87/1.00  bmc1_current_bound:                     -1
% 2.87/1.00  bmc1_last_solved_bound:                 -1
% 2.87/1.00  bmc1_unsat_core_size:                   -1
% 2.87/1.00  bmc1_unsat_core_parents_size:           -1
% 2.87/1.00  bmc1_merge_next_fun:                    0
% 2.87/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.00  
% 2.87/1.00  ------ Instantiation
% 2.87/1.00  
% 2.87/1.00  inst_num_of_clauses:                    639
% 2.87/1.00  inst_num_in_passive:                    280
% 2.87/1.00  inst_num_in_active:                     310
% 2.87/1.00  inst_num_in_unprocessed:                49
% 2.87/1.00  inst_num_of_loops:                      310
% 2.87/1.00  inst_num_of_learning_restarts:          0
% 2.87/1.00  inst_num_moves_active_passive:          0
% 2.87/1.00  inst_lit_activity:                      0
% 2.87/1.00  inst_lit_activity_moves:                0
% 2.87/1.00  inst_num_tautologies:                   0
% 2.87/1.00  inst_num_prop_implied:                  0
% 2.87/1.00  inst_num_existing_simplified:           0
% 2.87/1.00  inst_num_eq_res_simplified:             0
% 2.87/1.00  inst_num_child_elim:                    0
% 2.87/1.00  inst_num_of_dismatching_blockings:      0
% 2.87/1.00  inst_num_of_non_proper_insts:           597
% 2.87/1.00  inst_num_of_duplicates:                 0
% 2.87/1.00  inst_inst_num_from_inst_to_res:         0
% 2.87/1.00  inst_dismatching_checking_time:         0.
% 2.87/1.00  
% 2.87/1.00  ------ Resolution
% 2.87/1.00  
% 2.87/1.00  res_num_of_clauses:                     0
% 2.87/1.00  res_num_in_passive:                     0
% 2.87/1.00  res_num_in_active:                      0
% 2.87/1.00  res_num_of_loops:                       91
% 2.87/1.00  res_forward_subset_subsumed:            5
% 2.87/1.00  res_backward_subset_subsumed:           0
% 2.87/1.00  res_forward_subsumed:                   0
% 2.87/1.00  res_backward_subsumed:                  0
% 2.87/1.00  res_forward_subsumption_resolution:     0
% 2.87/1.00  res_backward_subsumption_resolution:    0
% 2.87/1.00  res_clause_to_clause_subsumption:       303
% 2.87/1.00  res_orphan_elimination:                 0
% 2.87/1.00  res_tautology_del:                      0
% 2.87/1.00  res_num_eq_res_simplified:              0
% 2.87/1.00  res_num_sel_changes:                    0
% 2.87/1.00  res_moves_from_active_to_pass:          0
% 2.87/1.00  
% 2.87/1.00  ------ Superposition
% 2.87/1.00  
% 2.87/1.00  sup_time_total:                         0.
% 2.87/1.00  sup_time_generating:                    0.
% 2.87/1.00  sup_time_sim_full:                      0.
% 2.87/1.00  sup_time_sim_immed:                     0.
% 2.87/1.00  
% 2.87/1.00  sup_num_of_clauses:                     52
% 2.87/1.00  sup_num_in_active:                      14
% 2.87/1.00  sup_num_in_passive:                     38
% 2.87/1.00  sup_num_of_loops:                       60
% 2.87/1.00  sup_fw_superposition:                   31
% 2.87/1.00  sup_bw_superposition:                   135
% 2.87/1.00  sup_immediate_simplified:               35
% 2.87/1.00  sup_given_eliminated:                   2
% 2.87/1.00  comparisons_done:                       0
% 2.87/1.00  comparisons_avoided:                    142
% 2.87/1.00  
% 2.87/1.00  ------ Simplifications
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  sim_fw_subset_subsumed:                 14
% 2.87/1.00  sim_bw_subset_subsumed:                 7
% 2.87/1.00  sim_fw_subsumed:                        14
% 2.87/1.00  sim_bw_subsumed:                        1
% 2.87/1.00  sim_fw_subsumption_res:                 1
% 2.87/1.00  sim_bw_subsumption_res:                 0
% 2.87/1.00  sim_tautology_del:                      0
% 2.87/1.00  sim_eq_tautology_del:                   0
% 2.87/1.00  sim_eq_res_simp:                        0
% 2.87/1.00  sim_fw_demodulated:                     7
% 2.87/1.00  sim_bw_demodulated:                     42
% 2.87/1.00  sim_light_normalised:                   13
% 2.87/1.00  sim_joinable_taut:                      0
% 2.87/1.00  sim_joinable_simp:                      0
% 2.87/1.00  sim_ac_normalised:                      0
% 2.87/1.00  sim_smt_subsumption:                    0
% 2.87/1.00  
%------------------------------------------------------------------------------
