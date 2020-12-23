%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:20 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  122 (8640 expanded)
%              Number of clauses        :   68 (2709 expanded)
%              Number of leaves         :   15 (2434 expanded)
%              Depth                    :   24
%              Number of atoms          :  615 (62354 expanded)
%              Number of equality atoms :  483 (40114 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f21,plain,
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
   => ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK8 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != sK9
                      | ~ m1_subset_1(X9,sK7) )
                  | ~ m1_subset_1(X8,sK6) )
              | ~ m1_subset_1(X7,sK5) )
          | ~ m1_subset_1(X6,sK4) )
      & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK8 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != sK9
                    | ~ m1_subset_1(X9,sK7) )
                | ~ m1_subset_1(X8,sK6) )
            | ~ m1_subset_1(X7,sK5) )
        | ~ m1_subset_1(X6,sK4) )
    & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f21])).

fof(f41,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f65,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X6
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
          ( X4 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X5
          & m1_subset_1(X9,X3) )
     => ( X4 != X6
        & k4_mcart_1(X6,X7,X8,sK3(X0,X1,X2,X3,X4,X5)) = X5
        & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ? [X9] :
              ( X4 != X6
              & k4_mcart_1(X6,X7,X8,X9) = X5
              & m1_subset_1(X9,X3) )
          & m1_subset_1(X8,X2) )
     => ( ? [X9] :
            ( X4 != X6
            & k4_mcart_1(X6,X7,sK2(X0,X1,X2,X3,X4,X5),X9) = X5
            & m1_subset_1(X9,X3) )
        & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( ? [X9] :
                  ( X4 != X6
                  & k4_mcart_1(X6,X7,X8,X9) = X5
                  & m1_subset_1(X9,X3) )
              & m1_subset_1(X8,X2) )
          & m1_subset_1(X7,X1) )
     => ( ? [X8] :
            ( ? [X9] :
                ( X4 != X6
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
                      ( X4 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
     => ( ? [X7] :
            ( ? [X8] :
                ( ? [X9] :
                    ( sK0(X0,X1,X2,X3,X4,X5) != X4
                    & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5
                    & m1_subset_1(X9,X3) )
                & m1_subset_1(X8,X2) )
            & m1_subset_1(X7,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ( sK0(X0,X1,X2,X3,X4,X5) != X4
        & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5
        & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)
        & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)
        & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)
        & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f19,f18,f17,f16])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5)),sK2(X0,X1,X2,X3,X4,X5)),sK3(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f39,f48,f49])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f43,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X7
      | k4_mcart_1(X6,X7,X8,X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X7
      | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f5,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f48,f49])).

fof(f68,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f52])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f47,plain,(
    k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_451,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X5,X0),sK1(X1,X2,X3,X4,X5,X0)),sK2(X1,X2,X3,X4,X5,X0)),sK3(X1,X2,X3,X4,X5,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_457,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X5,X4),sK1(X0,X1,X2,X3,X5,X4)),sK2(X0,X1,X2,X3,X5,X4)),sK3(X0,X1,X2,X3,X5,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3643,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_457])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_459,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1375,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_459])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_192,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_213,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_193,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_708,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_709,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_710,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_711,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_712,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_713,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_714,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_715,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1814,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1375,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_3644,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3643,c_1814])).

cnf(c_3646,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3644,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ m1_subset_1(X1,sK6)
    | ~ m1_subset_1(X2,sK5)
    | ~ m1_subset_1(X3,sK4)
    | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK9
    | sK8 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_452,plain,
    ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK9
    | sK8 = X1
    | m1_subset_1(X3,sK7) != iProver_top
    | m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3665,plain,
    ( sK1(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3646,c_452])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK0(X1,X2,X3,X4,X5,X0),X1)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_453,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2,X3,X5,X4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1216,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_453])).

cnf(c_2255,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1216,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_2261,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2255,c_1814])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK1(X1,X2,X3,X4,X5,X0),X2)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_454,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X3,X5,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2275,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_454])).

cnf(c_2276,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2275,c_1814])).

cnf(c_2485,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2276,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK2(X1,X2,X3,X4,X5,X0),X3)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_455,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2,X3,X5,X4),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2501,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_455])).

cnf(c_2502,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2501,c_1814])).

cnf(c_3185,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2502,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK3(X1,X2,X3,X4,X5,X0),X4)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_456,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2,X3,X5,X4),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2734,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_456])).

cnf(c_2735,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2734,c_1814])).

cnf(c_3194,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2735,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_3896,plain,
    ( sK1(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3665,c_2261,c_2485,c_3185,c_3194])).

cnf(c_3901,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(superposition,[status(thm)],[c_3896,c_3646])).

cnf(c_2,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k9_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X1
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_464,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4163,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X4,sK9)),sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3901,c_464])).

cnf(c_4467,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_4163])).

cnf(c_4469,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4467,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_4474,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(superposition,[status(thm)],[c_3901,c_4469])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_460,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1383,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_460])).

cnf(c_2029,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1383,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_4487,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = sK8 ),
    inference(demodulation,[status(thm)],[c_4474,c_2029])).

cnf(c_14,negated_conjecture,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2032,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) != sK8 ),
    inference(demodulation,[status(thm)],[c_2029,c_14])).

cnf(c_4538,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4487,c_2032])).

cnf(c_4844,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_4538,c_4538])).

cnf(c_5369,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_4844,c_18])).

cnf(c_5371,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5369,c_4844])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.01/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.99  
% 3.01/0.99  ------  iProver source info
% 3.01/0.99  
% 3.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.99  git: non_committed_changes: false
% 3.01/0.99  git: last_make_outside_of_git: false
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     num_symb
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       true
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     false
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   []
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_full_bw                           [BwDemod]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  ------ Parsing...
% 3.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.99  ------ Proving...
% 3.01/0.99  ------ Problem Properties 
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  clauses                                 21
% 3.01/0.99  conjectures                             7
% 3.01/0.99  EPR                                     4
% 3.01/0.99  Horn                                    7
% 3.01/0.99  unary                                   6
% 3.01/0.99  binary                                  0
% 3.01/0.99  lits                                    102
% 3.01/0.99  lits eq                                 79
% 3.01/0.99  fd_pure                                 0
% 3.01/0.99  fd_pseudo                               0
% 3.01/0.99  fd_cond                                 5
% 3.01/0.99  fd_pseudo_cond                          5
% 3.01/0.99  AC symbols                              0
% 3.01/0.99  
% 3.01/0.99  ------ Schedule dynamic 5 is on 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  Current options:
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     none
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       false
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     false
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   []
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_full_bw                           [BwDemod]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ Proving...
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS status Theorem for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99   Resolution empty clause
% 3.01/0.99  
% 3.01/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  fof(f8,conjecture,(
% 3.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f9,negated_conjecture,(
% 3.01/0.99    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.01/0.99    inference(negated_conjecture,[],[f8])).
% 3.01/0.99  
% 3.01/0.99  fof(f14,plain,(
% 3.01/0.99    ? [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.01/0.99    inference(ennf_transformation,[],[f9])).
% 3.01/0.99  
% 3.01/0.99  fof(f15,plain,(
% 3.01/0.99    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.01/0.99    inference(flattening,[],[f14])).
% 3.01/0.99  
% 3.01/0.99  fof(f21,plain,(
% 3.01/0.99    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f22,plain,(
% 3.01/0.99    k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f21])).
% 3.01/0.99  
% 3.01/0.99  fof(f41,plain,(
% 3.01/0.99    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f4,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f26,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f4])).
% 3.01/0.99  
% 3.01/0.99  fof(f2,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f24,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f2])).
% 3.01/0.99  
% 3.01/0.99  fof(f49,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f26,f24])).
% 3.01/0.99  
% 3.01/0.99  fof(f65,plain,(
% 3.01/0.99    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 3.01/0.99    inference(definition_unfolding,[],[f41,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f7,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f12,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.01/0.99    inference(ennf_transformation,[],[f7])).
% 3.01/0.99  
% 3.01/0.99  fof(f13,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.01/0.99    inference(flattening,[],[f12])).
% 3.01/0.99  
% 3.01/0.99  fof(f19,plain,(
% 3.01/0.99    ( ! [X6,X8,X7] : (! [X5,X4,X3,X2,X1,X0] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) => (X4 != X6 & k4_mcart_1(X6,X7,X8,sK3(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f18,plain,(
% 3.01/0.99    ( ! [X6,X7] : (! [X5,X4,X3,X2,X1,X0] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) => (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,sK2(X0,X1,X2,X3,X4,X5),X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f17,plain,(
% 3.01/0.99    ( ! [X6] : (! [X5,X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) => (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,sK1(X0,X1,X2,X3,X4,X5),X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f16,plain,(
% 3.01/0.99    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) => (? [X7] : (? [X8] : (? [X9] : (sK0(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f20,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ((((sK0(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f19,f18,f17,f16])).
% 3.01/0.99  
% 3.01/0.99  fof(f39,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f3,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f25,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f3])).
% 3.01/0.99  
% 3.01/0.99  fof(f1,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f23,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f1])).
% 3.01/0.99  
% 3.01/0.99  fof(f48,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f25,f23])).
% 3.01/0.99  
% 3.01/0.99  fof(f59,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5)),sK2(X0,X1,X2,X3,X4,X5)),sK3(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.01/0.99    inference(definition_unfolding,[],[f39,f48,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f6,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f11,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.01/0.99    inference(ennf_transformation,[],[f6])).
% 3.01/0.99  
% 3.01/0.99  fof(f31,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.01/0.99    inference(cnf_transformation,[],[f11])).
% 3.01/0.99  
% 3.01/0.99  fof(f57,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.01/0.99    inference(definition_unfolding,[],[f31,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f43,plain,(
% 3.01/0.99    k1_xboole_0 != sK4),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f44,plain,(
% 3.01/0.99    k1_xboole_0 != sK5),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f45,plain,(
% 3.01/0.99    k1_xboole_0 != sK6),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f46,plain,(
% 3.01/0.99    k1_xboole_0 != sK7),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f42,plain,(
% 3.01/0.99    ( ! [X6,X8,X7,X9] : (sK8 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f64,plain,(
% 3.01/0.99    ( ! [X6,X8,X7,X9] : (sK8 = X7 | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f42,f48])).
% 3.01/0.99  
% 3.01/0.99  fof(f35,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f63,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.01/0.99    inference(definition_unfolding,[],[f35,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f36,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f62,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.01/0.99    inference(definition_unfolding,[],[f36,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f37,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f61,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.01/0.99    inference(definition_unfolding,[],[f37,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f38,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f60,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.01/0.99    inference(definition_unfolding,[],[f38,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f5,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f10,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.01/0.99    inference(ennf_transformation,[],[f5])).
% 3.01/0.99  
% 3.01/0.99  fof(f28,plain,(
% 3.01/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.01/0.99    inference(cnf_transformation,[],[f10])).
% 3.01/0.99  
% 3.01/0.99  fof(f52,plain,(
% 3.01/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.01/0.99    inference(definition_unfolding,[],[f28,f48,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f68,plain,(
% 3.01/0.99    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.01/0.99    inference(equality_resolution,[],[f52])).
% 3.01/0.99  
% 3.01/0.99  fof(f32,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.01/0.99    inference(cnf_transformation,[],[f11])).
% 3.01/0.99  
% 3.01/0.99  fof(f56,plain,(
% 3.01/0.99    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.01/0.99    inference(definition_unfolding,[],[f32,f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f47,plain,(
% 3.01/0.99    k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  cnf(c_20,negated_conjecture,
% 3.01/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_451,plain,
% 3.01/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.01/0.99      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 3.01/0.99      | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X5,X0),sK1(X1,X2,X3,X4,X5,X0)),sK2(X1,X2,X3,X4,X5,X0)),sK3(X1,X2,X3,X4,X5,X0)) = X0
% 3.01/0.99      | k1_xboole_0 = X4
% 3.01/0.99      | k1_xboole_0 = X3
% 3.01/0.99      | k1_xboole_0 = X2
% 3.01/0.99      | k1_xboole_0 = X1 ),
% 3.01/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_457,plain,
% 3.01/0.99      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 3.01/0.99      | k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X5,X4),sK1(X0,X1,X2,X3,X5,X4)),sK2(X0,X1,X2,X3,X5,X4)),sK3(X0,X1,X2,X3,X5,X4)) = X4
% 3.01/0.99      | k1_xboole_0 = X2
% 3.01/0.99      | k1_xboole_0 = X1
% 3.01/0.99      | k1_xboole_0 = X0
% 3.01/0.99      | k1_xboole_0 = X3
% 3.01/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3643,plain,
% 3.01/0.99      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 3.01/0.99      | k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_457]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.01/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.01/1.00      | k1_xboole_0 = X4
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_459,plain,
% 3.01/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1375,plain,
% 3.01/1.00      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_459]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_18,negated_conjecture,
% 3.01/1.00      ( k1_xboole_0 != sK4 ),
% 3.01/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_17,negated_conjecture,
% 3.01/1.00      ( k1_xboole_0 != sK5 ),
% 3.01/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_16,negated_conjecture,
% 3.01/1.00      ( k1_xboole_0 != sK6 ),
% 3.01/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_15,negated_conjecture,
% 3.01/1.00      ( k1_xboole_0 != sK7 ),
% 3.01/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_192,plain,( X0 = X0 ),theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_213,plain,
% 3.01/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_192]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_193,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_708,plain,
% 3.01/1.00      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_709,plain,
% 3.01/1.00      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_708]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_710,plain,
% 3.01/1.00      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_711,plain,
% 3.01/1.00      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_710]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_712,plain,
% 3.01/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_713,plain,
% 3.01/1.00      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_712]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_714,plain,
% 3.01/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_715,plain,
% 3.01/1.00      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_714]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1814,plain,
% 3.01/1.00      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1375,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3644,plain,
% 3.01/1.00      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0 ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_3643,c_1814]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3646,plain,
% 3.01/1.00      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9)),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3644,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_19,negated_conjecture,
% 3.01/1.00      ( ~ m1_subset_1(X0,sK7)
% 3.01/1.00      | ~ m1_subset_1(X1,sK6)
% 3.01/1.00      | ~ m1_subset_1(X2,sK5)
% 3.01/1.00      | ~ m1_subset_1(X3,sK4)
% 3.01/1.00      | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK9
% 3.01/1.00      | sK8 = X2 ),
% 3.01/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_452,plain,
% 3.01/1.00      ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK9
% 3.01/1.00      | sK8 = X1
% 3.01/1.00      | m1_subset_1(X3,sK7) != iProver_top
% 3.01/1.00      | m1_subset_1(X2,sK6) != iProver_top
% 3.01/1.00      | m1_subset_1(X1,sK5) != iProver_top
% 3.01/1.00      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3665,plain,
% 3.01/1.00      ( sK1(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) != iProver_top
% 3.01/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 3.01/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 3.01/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3646,c_452]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_13,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.01/1.00      | m1_subset_1(sK0(X1,X2,X3,X4,X5,X0),X1)
% 3.01/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 3.01/1.00      | k1_xboole_0 = X4
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_453,plain,
% 3.01/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
% 3.01/1.00      | m1_subset_1(sK0(X0,X1,X2,X3,X5,X4),X0) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1216,plain,
% 3.01/1.00      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_453]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2255,plain,
% 3.01/1.00      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 3.01/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1216,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2261,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) = iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_2255,c_1814]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_12,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.01/1.00      | m1_subset_1(sK1(X1,X2,X3,X4,X5,X0),X2)
% 3.01/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 3.01/1.00      | k1_xboole_0 = X4
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_454,plain,
% 3.01/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
% 3.01/1.00      | m1_subset_1(sK1(X0,X1,X2,X3,X5,X4),X1) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2275,plain,
% 3.01/1.00      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_454]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2276,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) = iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_2275,c_1814]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2485,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2276,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_11,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.01/1.00      | m1_subset_1(sK2(X1,X2,X3,X4,X5,X0),X3)
% 3.01/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 3.01/1.00      | k1_xboole_0 = X4
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_455,plain,
% 3.01/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
% 3.01/1.00      | m1_subset_1(sK2(X0,X1,X2,X3,X5,X4),X2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2501,plain,
% 3.01/1.00      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_455]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2502,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) = iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_2501,c_1814]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3185,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2502,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_10,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.01/1.00      | m1_subset_1(sK3(X1,X2,X3,X4,X5,X0),X4)
% 3.01/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 3.01/1.00      | k1_xboole_0 = X4
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_456,plain,
% 3.01/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top
% 3.01/1.00      | m1_subset_1(sK3(X0,X1,X2,X3,X5,X4),X3) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2734,plain,
% 3.01/1.00      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_456]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2735,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) = iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_2734,c_1814]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3194,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2735,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3896,plain,
% 3.01/1.00      ( sK1(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3665,c_2261,c_2485,c_3185,c_3194]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3901,plain,
% 3.01/1.00      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3896,c_3646]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2,plain,
% 3.01/1.00      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
% 3.01/1.00      | k9_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X1
% 3.01/1.00      | k1_xboole_0 = X7
% 3.01/1.00      | k1_xboole_0 = X6
% 3.01/1.00      | k1_xboole_0 = X5
% 3.01/1.00      | k1_xboole_0 = X4 ),
% 3.01/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_464,plain,
% 3.01/1.00      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4163,plain,
% 3.01/1.00      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X4,sK9)),sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK8
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X4
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3901,c_464]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4467,plain,
% 3.01/1.00      ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_4163]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4469,plain,
% 3.01/1.00      ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK8),sK2(sK4,sK5,sK6,sK7,X0,sK9)),sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4467,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4474,plain,
% 3.01/1.00      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
% 3.01/1.00      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3901,c_4469]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.01/1.00      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.01/1.00      | k1_xboole_0 = X4
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_460,plain,
% 3.01/1.00      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.01/1.00      | k1_xboole_0 = X2
% 3.01/1.00      | k1_xboole_0 = X1
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | k1_xboole_0 = X3
% 3.01/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1383,plain,
% 3.01/1.00      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 3.01/1.00      | sK7 = k1_xboole_0
% 3.01/1.00      | sK6 = k1_xboole_0
% 3.01/1.00      | sK5 = k1_xboole_0
% 3.01/1.00      | sK4 = k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_451,c_460]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2029,plain,
% 3.01/1.00      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1383,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4487,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 3.01/1.00      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = sK8 ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_4474,c_2029]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_14,negated_conjecture,
% 3.01/1.00      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
% 3.01/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2032,plain,
% 3.01/1.00      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) != sK8 ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_2029,c_14]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4538,plain,
% 3.01/1.00      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 3.01/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4487,c_2032]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4844,plain,
% 3.01/1.00      ( X0 = X1 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4538,c_4538]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5369,plain,
% 3.01/1.00      ( k1_xboole_0 != X0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4844,c_18]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5371,plain,
% 3.01/1.00      ( $false ),
% 3.01/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5369,c_4844]) ).
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  ------                               Statistics
% 3.01/1.00  
% 3.01/1.00  ------ General
% 3.01/1.00  
% 3.01/1.00  abstr_ref_over_cycles:                  0
% 3.01/1.00  abstr_ref_under_cycles:                 0
% 3.01/1.00  gc_basic_clause_elim:                   0
% 3.01/1.00  forced_gc_time:                         0
% 3.01/1.00  parsing_time:                           0.009
% 3.01/1.00  unif_index_cands_time:                  0.
% 3.01/1.00  unif_index_add_time:                    0.
% 3.01/1.00  orderings_time:                         0.
% 3.01/1.00  out_proof_time:                         0.012
% 3.01/1.00  total_time:                             0.218
% 3.01/1.00  num_of_symbols:                         51
% 3.01/1.00  num_of_terms:                           10579
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing
% 3.01/1.00  
% 3.01/1.00  num_of_splits:                          0
% 3.01/1.00  num_of_split_atoms:                     0
% 3.01/1.00  num_of_reused_defs:                     0
% 3.01/1.00  num_eq_ax_congr_red:                    72
% 3.01/1.00  num_of_sem_filtered_clauses:            1
% 3.01/1.00  num_of_subtypes:                        0
% 3.01/1.00  monotx_restored_types:                  0
% 3.01/1.00  sat_num_of_epr_types:                   0
% 3.01/1.00  sat_num_of_non_cyclic_types:            0
% 3.01/1.00  sat_guarded_non_collapsed_types:        0
% 3.01/1.00  num_pure_diseq_elim:                    0
% 3.01/1.00  simp_replaced_by:                       0
% 3.01/1.00  res_preprocessed:                       86
% 3.01/1.00  prep_upred:                             0
% 3.01/1.00  prep_unflattend:                        0
% 3.01/1.00  smt_new_axioms:                         0
% 3.01/1.00  pred_elim_cands:                        1
% 3.01/1.00  pred_elim:                              0
% 3.01/1.00  pred_elim_cl:                           0
% 3.01/1.00  pred_elim_cycles:                       1
% 3.01/1.00  merged_defs:                            0
% 3.01/1.00  merged_defs_ncl:                        0
% 3.01/1.00  bin_hyper_res:                          0
% 3.01/1.00  prep_cycles:                            3
% 3.01/1.00  pred_elim_time:                         0.
% 3.01/1.00  splitting_time:                         0.
% 3.01/1.00  sem_filter_time:                        0.
% 3.01/1.00  monotx_time:                            0.
% 3.01/1.00  subtype_inf_time:                       0.
% 3.01/1.00  
% 3.01/1.00  ------ Problem properties
% 3.01/1.00  
% 3.01/1.00  clauses:                                21
% 3.01/1.00  conjectures:                            7
% 3.01/1.00  epr:                                    4
% 3.01/1.00  horn:                                   7
% 3.01/1.00  ground:                                 6
% 3.01/1.00  unary:                                  6
% 3.01/1.00  binary:                                 0
% 3.01/1.00  lits:                                   102
% 3.01/1.00  lits_eq:                                79
% 3.01/1.00  fd_pure:                                0
% 3.01/1.00  fd_pseudo:                              0
% 3.01/1.00  fd_cond:                                5
% 3.01/1.00  fd_pseudo_cond:                         5
% 3.01/1.00  ac_symbols:                             0
% 3.01/1.00  
% 3.01/1.00  ------ Propositional Solver
% 3.01/1.00  
% 3.01/1.00  prop_solver_calls:                      22
% 3.01/1.00  prop_fast_solver_calls:                 1199
% 3.01/1.00  smt_solver_calls:                       0
% 3.01/1.00  smt_fast_solver_calls:                  0
% 3.01/1.00  prop_num_of_clauses:                    1989
% 3.01/1.00  prop_preprocess_simplified:             7225
% 3.01/1.00  prop_fo_subsumed:                       60
% 3.01/1.00  prop_solver_time:                       0.
% 3.01/1.00  smt_solver_time:                        0.
% 3.01/1.00  smt_fast_solver_time:                   0.
% 3.01/1.00  prop_fast_solver_time:                  0.
% 3.01/1.00  prop_unsat_core_time:                   0.
% 3.01/1.00  
% 3.01/1.00  ------ QBF
% 3.01/1.00  
% 3.01/1.00  qbf_q_res:                              0
% 3.01/1.00  qbf_num_tautologies:                    0
% 3.01/1.00  qbf_prep_cycles:                        0
% 3.01/1.00  
% 3.01/1.00  ------ BMC1
% 3.01/1.00  
% 3.01/1.00  bmc1_current_bound:                     -1
% 3.01/1.00  bmc1_last_solved_bound:                 -1
% 3.01/1.00  bmc1_unsat_core_size:                   -1
% 3.01/1.00  bmc1_unsat_core_parents_size:           -1
% 3.01/1.00  bmc1_merge_next_fun:                    0
% 3.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation
% 3.01/1.00  
% 3.01/1.00  inst_num_of_clauses:                    607
% 3.01/1.00  inst_num_in_passive:                    172
% 3.01/1.00  inst_num_in_active:                     370
% 3.01/1.00  inst_num_in_unprocessed:                65
% 3.01/1.00  inst_num_of_loops:                      370
% 3.01/1.00  inst_num_of_learning_restarts:          0
% 3.01/1.00  inst_num_moves_active_passive:          0
% 3.01/1.00  inst_lit_activity:                      0
% 3.01/1.00  inst_lit_activity_moves:                0
% 3.01/1.00  inst_num_tautologies:                   0
% 3.01/1.00  inst_num_prop_implied:                  0
% 3.01/1.00  inst_num_existing_simplified:           0
% 3.01/1.00  inst_num_eq_res_simplified:             0
% 3.01/1.00  inst_num_child_elim:                    0
% 3.01/1.00  inst_num_of_dismatching_blockings:      0
% 3.01/1.00  inst_num_of_non_proper_insts:           569
% 3.01/1.00  inst_num_of_duplicates:                 0
% 3.01/1.00  inst_inst_num_from_inst_to_res:         0
% 3.01/1.00  inst_dismatching_checking_time:         0.
% 3.01/1.00  
% 3.01/1.00  ------ Resolution
% 3.01/1.00  
% 3.01/1.00  res_num_of_clauses:                     0
% 3.01/1.00  res_num_in_passive:                     0
% 3.01/1.00  res_num_in_active:                      0
% 3.01/1.00  res_num_of_loops:                       89
% 3.01/1.00  res_forward_subset_subsumed:            5
% 3.01/1.00  res_backward_subset_subsumed:           0
% 3.01/1.00  res_forward_subsumed:                   0
% 3.01/1.00  res_backward_subsumed:                  0
% 3.01/1.00  res_forward_subsumption_resolution:     0
% 3.01/1.00  res_backward_subsumption_resolution:    0
% 3.01/1.00  res_clause_to_clause_subsumption:       154
% 3.01/1.00  res_orphan_elimination:                 0
% 3.01/1.00  res_tautology_del:                      0
% 3.01/1.00  res_num_eq_res_simplified:              0
% 3.01/1.00  res_num_sel_changes:                    0
% 3.01/1.00  res_moves_from_active_to_pass:          0
% 3.01/1.00  
% 3.01/1.00  ------ Superposition
% 3.01/1.00  
% 3.01/1.00  sup_time_total:                         0.
% 3.01/1.00  sup_time_generating:                    0.
% 3.01/1.00  sup_time_sim_full:                      0.
% 3.01/1.00  sup_time_sim_immed:                     0.
% 3.01/1.00  
% 3.01/1.00  sup_num_of_clauses:                     48
% 3.01/1.00  sup_num_in_active:                      16
% 3.01/1.00  sup_num_in_passive:                     32
% 3.01/1.00  sup_num_of_loops:                       72
% 3.01/1.00  sup_fw_superposition:                   26
% 3.01/1.00  sup_bw_superposition:                   173
% 3.01/1.00  sup_immediate_simplified:               43
% 3.01/1.00  sup_given_eliminated:                   3
% 3.01/1.00  comparisons_done:                       0
% 3.01/1.00  comparisons_avoided:                    100
% 3.01/1.00  
% 3.01/1.00  ------ Simplifications
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  sim_fw_subset_subsumed:                 14
% 3.01/1.00  sim_bw_subset_subsumed:                 7
% 3.01/1.00  sim_fw_subsumed:                        22
% 3.01/1.00  sim_bw_subsumed:                        1
% 3.01/1.00  sim_fw_subsumption_res:                 1
% 3.01/1.00  sim_bw_subsumption_res:                 0
% 3.01/1.00  sim_tautology_del:                      0
% 3.01/1.00  sim_eq_tautology_del:                   2
% 3.01/1.00  sim_eq_res_simp:                        0
% 3.01/1.00  sim_fw_demodulated:                     10
% 3.01/1.00  sim_bw_demodulated:                     51
% 3.01/1.00  sim_light_normalised:                   16
% 3.01/1.00  sim_joinable_taut:                      0
% 3.01/1.00  sim_joinable_simp:                      0
% 3.01/1.00  sim_ac_normalised:                      0
% 3.01/1.00  sim_smt_subsumption:                    0
% 3.01/1.00  
%------------------------------------------------------------------------------
