%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:24 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  135 (2262 expanded)
%              Number of clauses        :   74 ( 657 expanded)
%              Number of leaves         :   15 ( 666 expanded)
%              Depth                    :   21
%              Number of atoms          :  667 (15417 expanded)
%              Number of equality atoms :  529 (9765 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    8 (   1 average)

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
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f13])).

fof(f20,plain,
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

fof(f21,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f20])).

fof(f39,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f62,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(X5,X6,X7,X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(X5,X6,X7,sK3(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(X5,X6,X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18,f17,f16,f15])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f46,f47])).

fof(f41,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X9
      | k4_mcart_1(X6,X7,X8,X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X9
      | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f47])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f46,f47])).

fof(f66,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f56])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f46,f47])).

fof(f65,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f55])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f46,f47])).

fof(f63,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f53])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f45,plain,(
    k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_426,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)),sK3(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_440,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3554,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_426,c_440])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_181,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_202,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_182,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_656,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_657,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_658,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_659,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_660,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_661,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_662,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_663,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_3555,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3554,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ m1_subset_1(X1,sK6)
    | ~ m1_subset_1(X2,sK5)
    | ~ m1_subset_1(X3,sK4)
    | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK9
    | sK8 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_427,plain,
    ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK9
    | sK8 = X3
    | m1_subset_1(X3,sK7) != iProver_top
    | m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3560,plain,
    ( sK3(sK4,sK5,sK6,sK7,sK9) = sK8
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_427])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_436,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK0(X2,X1,X0,X3,X4),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1336,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_436])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_437,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK1(X2,X1,X0,X3,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1345,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_437])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_438,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK2(X2,X1,X0,X3,X4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1494,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_438])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK3(X1,X2,X3,X4,X0),X4)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_439,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK3(X2,X1,X0,X3,X4),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2452,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_439])).

cnf(c_3783,plain,
    ( sK3(sK4,sK5,sK6,sK7,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3560,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663,c_1336,c_1345,c_1494,c_2452])).

cnf(c_3786,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK8) = sK9 ),
    inference(demodulation,[status(thm)],[c_3783,c_3555])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k8_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X0
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_432,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3572,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9))) = sK0(sK4,sK5,sK6,sK7,sK9)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_432])).

cnf(c_3579,plain,
    ( k8_mcart_1(X0,X1,X2,X3,sK9) = sK0(sK4,sK5,sK6,sK7,sK9)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3572,c_3555])).

cnf(c_3855,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK0(sK4,sK5,sK6,sK7,sK9)
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_426,c_3579])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_428,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1180,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_426,c_428])).

cnf(c_2238,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1180,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663])).

cnf(c_3856,plain,
    ( sK0(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3855,c_2238])).

cnf(c_3857,plain,
    ( sK0(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3856,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663])).

cnf(c_7,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k9_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X1
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_433,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3571,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9))) = sK1(sK4,sK5,sK6,sK7,sK9)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_433])).

cnf(c_3592,plain,
    ( k9_mcart_1(X0,X1,X2,X3,sK9) = sK1(sK4,sK5,sK6,sK7,sK9)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3571,c_3555])).

cnf(c_3945,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK1(sK4,sK5,sK6,sK7,sK9)
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_426,c_3592])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_429,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2461,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_426,c_429])).

cnf(c_3140,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2461,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663])).

cnf(c_3946,plain,
    ( sK1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3945,c_3140])).

cnf(c_3947,plain,
    ( sK1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3946,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663])).

cnf(c_3965,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))),sK2(sK4,sK5,sK6,sK7,sK9)),sK8) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_3786,c_3857,c_3947])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k11_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X3
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_435,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3978,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))),sK2(sK4,sK5,sK6,sK7,sK9)),sK8)) = sK8
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_435])).

cnf(c_4009,plain,
    ( k11_mcart_1(X0,X1,X2,X3,sK9) = sK8
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3978,c_3965])).

cnf(c_4242,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_426,c_4009])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_431,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_970,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9)
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_426,c_431])).

cnf(c_1496,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_970,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663])).

cnf(c_4243,plain,
    ( k2_mcart_1(sK9) = sK8
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4242,c_1496])).

cnf(c_13,negated_conjecture,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1499,plain,
    ( k2_mcart_1(sK9) != sK8 ),
    inference(demodulation,[status(thm)],[c_1496,c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4243,c_1499,c_663,c_661,c_659,c_657,c_202,c_14,c_15,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.27/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.02  
% 2.27/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/1.02  
% 2.27/1.02  ------  iProver source info
% 2.27/1.02  
% 2.27/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.27/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/1.02  git: non_committed_changes: false
% 2.27/1.02  git: last_make_outside_of_git: false
% 2.27/1.02  
% 2.27/1.02  ------ 
% 2.27/1.02  
% 2.27/1.02  ------ Input Options
% 2.27/1.02  
% 2.27/1.02  --out_options                           all
% 2.27/1.02  --tptp_safe_out                         true
% 2.27/1.02  --problem_path                          ""
% 2.27/1.02  --include_path                          ""
% 2.27/1.02  --clausifier                            res/vclausify_rel
% 2.27/1.02  --clausifier_options                    --mode clausify
% 2.27/1.02  --stdin                                 false
% 2.27/1.02  --stats_out                             all
% 2.27/1.02  
% 2.27/1.02  ------ General Options
% 2.27/1.02  
% 2.27/1.02  --fof                                   false
% 2.27/1.02  --time_out_real                         305.
% 2.27/1.02  --time_out_virtual                      -1.
% 2.27/1.02  --symbol_type_check                     false
% 2.27/1.02  --clausify_out                          false
% 2.27/1.02  --sig_cnt_out                           false
% 2.27/1.02  --trig_cnt_out                          false
% 2.27/1.02  --trig_cnt_out_tolerance                1.
% 2.27/1.02  --trig_cnt_out_sk_spl                   false
% 2.27/1.02  --abstr_cl_out                          false
% 2.27/1.02  
% 2.27/1.02  ------ Global Options
% 2.27/1.02  
% 2.27/1.02  --schedule                              default
% 2.27/1.02  --add_important_lit                     false
% 2.27/1.02  --prop_solver_per_cl                    1000
% 2.27/1.02  --min_unsat_core                        false
% 2.27/1.02  --soft_assumptions                      false
% 2.27/1.02  --soft_lemma_size                       3
% 2.27/1.02  --prop_impl_unit_size                   0
% 2.27/1.02  --prop_impl_unit                        []
% 2.27/1.02  --share_sel_clauses                     true
% 2.27/1.02  --reset_solvers                         false
% 2.27/1.02  --bc_imp_inh                            [conj_cone]
% 2.27/1.02  --conj_cone_tolerance                   3.
% 2.27/1.02  --extra_neg_conj                        none
% 2.27/1.02  --large_theory_mode                     true
% 2.27/1.02  --prolific_symb_bound                   200
% 2.27/1.02  --lt_threshold                          2000
% 2.27/1.02  --clause_weak_htbl                      true
% 2.27/1.02  --gc_record_bc_elim                     false
% 2.27/1.02  
% 2.27/1.02  ------ Preprocessing Options
% 2.27/1.02  
% 2.27/1.02  --preprocessing_flag                    true
% 2.27/1.02  --time_out_prep_mult                    0.1
% 2.27/1.02  --splitting_mode                        input
% 2.27/1.02  --splitting_grd                         true
% 2.27/1.02  --splitting_cvd                         false
% 2.27/1.02  --splitting_cvd_svl                     false
% 2.27/1.02  --splitting_nvd                         32
% 2.27/1.02  --sub_typing                            true
% 2.27/1.02  --prep_gs_sim                           true
% 2.27/1.02  --prep_unflatten                        true
% 2.27/1.02  --prep_res_sim                          true
% 2.27/1.02  --prep_upred                            true
% 2.27/1.02  --prep_sem_filter                       exhaustive
% 2.27/1.02  --prep_sem_filter_out                   false
% 2.27/1.02  --pred_elim                             true
% 2.27/1.02  --res_sim_input                         true
% 2.27/1.02  --eq_ax_congr_red                       true
% 2.27/1.02  --pure_diseq_elim                       true
% 2.27/1.02  --brand_transform                       false
% 2.27/1.02  --non_eq_to_eq                          false
% 2.27/1.02  --prep_def_merge                        true
% 2.27/1.02  --prep_def_merge_prop_impl              false
% 2.27/1.02  --prep_def_merge_mbd                    true
% 2.27/1.02  --prep_def_merge_tr_red                 false
% 2.27/1.02  --prep_def_merge_tr_cl                  false
% 2.27/1.02  --smt_preprocessing                     true
% 2.27/1.02  --smt_ac_axioms                         fast
% 2.27/1.02  --preprocessed_out                      false
% 2.27/1.02  --preprocessed_stats                    false
% 2.27/1.02  
% 2.27/1.02  ------ Abstraction refinement Options
% 2.27/1.02  
% 2.27/1.02  --abstr_ref                             []
% 2.27/1.02  --abstr_ref_prep                        false
% 2.27/1.02  --abstr_ref_until_sat                   false
% 2.27/1.02  --abstr_ref_sig_restrict                funpre
% 2.27/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.02  --abstr_ref_under                       []
% 2.27/1.02  
% 2.27/1.02  ------ SAT Options
% 2.27/1.02  
% 2.27/1.02  --sat_mode                              false
% 2.27/1.02  --sat_fm_restart_options                ""
% 2.27/1.02  --sat_gr_def                            false
% 2.27/1.02  --sat_epr_types                         true
% 2.27/1.02  --sat_non_cyclic_types                  false
% 2.27/1.02  --sat_finite_models                     false
% 2.27/1.02  --sat_fm_lemmas                         false
% 2.27/1.02  --sat_fm_prep                           false
% 2.27/1.02  --sat_fm_uc_incr                        true
% 2.27/1.02  --sat_out_model                         small
% 2.27/1.02  --sat_out_clauses                       false
% 2.27/1.02  
% 2.27/1.02  ------ QBF Options
% 2.27/1.02  
% 2.27/1.02  --qbf_mode                              false
% 2.27/1.02  --qbf_elim_univ                         false
% 2.27/1.02  --qbf_dom_inst                          none
% 2.27/1.02  --qbf_dom_pre_inst                      false
% 2.27/1.02  --qbf_sk_in                             false
% 2.27/1.02  --qbf_pred_elim                         true
% 2.27/1.02  --qbf_split                             512
% 2.27/1.02  
% 2.27/1.02  ------ BMC1 Options
% 2.27/1.02  
% 2.27/1.02  --bmc1_incremental                      false
% 2.27/1.02  --bmc1_axioms                           reachable_all
% 2.27/1.02  --bmc1_min_bound                        0
% 2.27/1.02  --bmc1_max_bound                        -1
% 2.27/1.02  --bmc1_max_bound_default                -1
% 2.27/1.02  --bmc1_symbol_reachability              true
% 2.27/1.02  --bmc1_property_lemmas                  false
% 2.27/1.02  --bmc1_k_induction                      false
% 2.27/1.02  --bmc1_non_equiv_states                 false
% 2.27/1.02  --bmc1_deadlock                         false
% 2.27/1.02  --bmc1_ucm                              false
% 2.27/1.02  --bmc1_add_unsat_core                   none
% 2.27/1.02  --bmc1_unsat_core_children              false
% 2.27/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.02  --bmc1_out_stat                         full
% 2.27/1.02  --bmc1_ground_init                      false
% 2.27/1.02  --bmc1_pre_inst_next_state              false
% 2.27/1.02  --bmc1_pre_inst_state                   false
% 2.27/1.02  --bmc1_pre_inst_reach_state             false
% 2.27/1.02  --bmc1_out_unsat_core                   false
% 2.27/1.02  --bmc1_aig_witness_out                  false
% 2.27/1.02  --bmc1_verbose                          false
% 2.27/1.02  --bmc1_dump_clauses_tptp                false
% 2.27/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.02  --bmc1_dump_file                        -
% 2.27/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.02  --bmc1_ucm_extend_mode                  1
% 2.27/1.02  --bmc1_ucm_init_mode                    2
% 2.27/1.02  --bmc1_ucm_cone_mode                    none
% 2.27/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.02  --bmc1_ucm_relax_model                  4
% 2.27/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.02  --bmc1_ucm_layered_model                none
% 2.27/1.02  --bmc1_ucm_max_lemma_size               10
% 2.27/1.02  
% 2.27/1.02  ------ AIG Options
% 2.27/1.02  
% 2.27/1.02  --aig_mode                              false
% 2.27/1.02  
% 2.27/1.02  ------ Instantiation Options
% 2.27/1.02  
% 2.27/1.02  --instantiation_flag                    true
% 2.27/1.02  --inst_sos_flag                         false
% 2.27/1.02  --inst_sos_phase                        true
% 2.27/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.02  --inst_lit_sel_side                     num_symb
% 2.27/1.02  --inst_solver_per_active                1400
% 2.27/1.02  --inst_solver_calls_frac                1.
% 2.27/1.02  --inst_passive_queue_type               priority_queues
% 2.27/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.02  --inst_passive_queues_freq              [25;2]
% 2.27/1.02  --inst_dismatching                      true
% 2.27/1.02  --inst_eager_unprocessed_to_passive     true
% 2.27/1.02  --inst_prop_sim_given                   true
% 2.27/1.02  --inst_prop_sim_new                     false
% 2.27/1.02  --inst_subs_new                         false
% 2.27/1.02  --inst_eq_res_simp                      false
% 2.27/1.02  --inst_subs_given                       false
% 2.27/1.02  --inst_orphan_elimination               true
% 2.27/1.02  --inst_learning_loop_flag               true
% 2.27/1.02  --inst_learning_start                   3000
% 2.27/1.02  --inst_learning_factor                  2
% 2.27/1.02  --inst_start_prop_sim_after_learn       3
% 2.27/1.02  --inst_sel_renew                        solver
% 2.27/1.02  --inst_lit_activity_flag                true
% 2.27/1.02  --inst_restr_to_given                   false
% 2.27/1.02  --inst_activity_threshold               500
% 2.27/1.02  --inst_out_proof                        true
% 2.27/1.02  
% 2.27/1.02  ------ Resolution Options
% 2.27/1.02  
% 2.27/1.02  --resolution_flag                       true
% 2.27/1.02  --res_lit_sel                           adaptive
% 2.27/1.02  --res_lit_sel_side                      none
% 2.27/1.02  --res_ordering                          kbo
% 2.27/1.02  --res_to_prop_solver                    active
% 2.27/1.02  --res_prop_simpl_new                    false
% 2.27/1.02  --res_prop_simpl_given                  true
% 2.27/1.02  --res_passive_queue_type                priority_queues
% 2.27/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.02  --res_passive_queues_freq               [15;5]
% 2.27/1.02  --res_forward_subs                      full
% 2.27/1.02  --res_backward_subs                     full
% 2.27/1.02  --res_forward_subs_resolution           true
% 2.27/1.02  --res_backward_subs_resolution          true
% 2.27/1.02  --res_orphan_elimination                true
% 2.27/1.02  --res_time_limit                        2.
% 2.27/1.02  --res_out_proof                         true
% 2.27/1.02  
% 2.27/1.02  ------ Superposition Options
% 2.27/1.02  
% 2.27/1.02  --superposition_flag                    true
% 2.27/1.02  --sup_passive_queue_type                priority_queues
% 2.27/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.02  --demod_completeness_check              fast
% 2.27/1.02  --demod_use_ground                      true
% 2.27/1.02  --sup_to_prop_solver                    passive
% 2.27/1.02  --sup_prop_simpl_new                    true
% 2.27/1.02  --sup_prop_simpl_given                  true
% 2.27/1.02  --sup_fun_splitting                     false
% 2.27/1.02  --sup_smt_interval                      50000
% 2.27/1.02  
% 2.27/1.02  ------ Superposition Simplification Setup
% 2.27/1.02  
% 2.27/1.02  --sup_indices_passive                   []
% 2.27/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.02  --sup_full_bw                           [BwDemod]
% 2.27/1.02  --sup_immed_triv                        [TrivRules]
% 2.27/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.02  --sup_immed_bw_main                     []
% 2.27/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.02  
% 2.27/1.02  ------ Combination Options
% 2.27/1.02  
% 2.27/1.02  --comb_res_mult                         3
% 2.27/1.02  --comb_sup_mult                         2
% 2.27/1.02  --comb_inst_mult                        10
% 2.27/1.02  
% 2.27/1.02  ------ Debug Options
% 2.27/1.02  
% 2.27/1.02  --dbg_backtrace                         false
% 2.27/1.02  --dbg_dump_prop_clauses                 false
% 2.27/1.02  --dbg_dump_prop_clauses_file            -
% 2.27/1.02  --dbg_out_stat                          false
% 2.27/1.02  ------ Parsing...
% 2.27/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/1.02  
% 2.27/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.27/1.02  
% 2.27/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/1.02  
% 2.27/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/1.02  ------ Proving...
% 2.27/1.02  ------ Problem Properties 
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  clauses                                 20
% 2.27/1.02  conjectures                             7
% 2.27/1.02  EPR                                     4
% 2.27/1.02  Horn                                    7
% 2.27/1.02  unary                                   6
% 2.27/1.02  binary                                  0
% 2.27/1.02  lits                                    90
% 2.27/1.02  lits eq                                 68
% 2.27/1.02  fd_pure                                 0
% 2.27/1.02  fd_pseudo                               0
% 2.27/1.02  fd_cond                                 9
% 2.27/1.02  fd_pseudo_cond                          0
% 2.27/1.02  AC symbols                              0
% 2.27/1.02  
% 2.27/1.02  ------ Schedule dynamic 5 is on 
% 2.27/1.02  
% 2.27/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  ------ 
% 2.27/1.02  Current options:
% 2.27/1.02  ------ 
% 2.27/1.02  
% 2.27/1.02  ------ Input Options
% 2.27/1.02  
% 2.27/1.02  --out_options                           all
% 2.27/1.02  --tptp_safe_out                         true
% 2.27/1.02  --problem_path                          ""
% 2.27/1.02  --include_path                          ""
% 2.27/1.02  --clausifier                            res/vclausify_rel
% 2.27/1.02  --clausifier_options                    --mode clausify
% 2.27/1.02  --stdin                                 false
% 2.27/1.02  --stats_out                             all
% 2.27/1.02  
% 2.27/1.02  ------ General Options
% 2.27/1.02  
% 2.27/1.02  --fof                                   false
% 2.27/1.02  --time_out_real                         305.
% 2.27/1.02  --time_out_virtual                      -1.
% 2.27/1.02  --symbol_type_check                     false
% 2.27/1.02  --clausify_out                          false
% 2.27/1.02  --sig_cnt_out                           false
% 2.27/1.02  --trig_cnt_out                          false
% 2.27/1.02  --trig_cnt_out_tolerance                1.
% 2.27/1.02  --trig_cnt_out_sk_spl                   false
% 2.27/1.02  --abstr_cl_out                          false
% 2.27/1.02  
% 2.27/1.02  ------ Global Options
% 2.27/1.02  
% 2.27/1.02  --schedule                              default
% 2.27/1.02  --add_important_lit                     false
% 2.27/1.02  --prop_solver_per_cl                    1000
% 2.27/1.02  --min_unsat_core                        false
% 2.27/1.02  --soft_assumptions                      false
% 2.27/1.02  --soft_lemma_size                       3
% 2.27/1.02  --prop_impl_unit_size                   0
% 2.27/1.02  --prop_impl_unit                        []
% 2.27/1.02  --share_sel_clauses                     true
% 2.27/1.02  --reset_solvers                         false
% 2.27/1.02  --bc_imp_inh                            [conj_cone]
% 2.27/1.02  --conj_cone_tolerance                   3.
% 2.27/1.02  --extra_neg_conj                        none
% 2.27/1.02  --large_theory_mode                     true
% 2.27/1.02  --prolific_symb_bound                   200
% 2.27/1.02  --lt_threshold                          2000
% 2.27/1.02  --clause_weak_htbl                      true
% 2.27/1.02  --gc_record_bc_elim                     false
% 2.27/1.02  
% 2.27/1.02  ------ Preprocessing Options
% 2.27/1.02  
% 2.27/1.02  --preprocessing_flag                    true
% 2.27/1.02  --time_out_prep_mult                    0.1
% 2.27/1.02  --splitting_mode                        input
% 2.27/1.02  --splitting_grd                         true
% 2.27/1.02  --splitting_cvd                         false
% 2.27/1.02  --splitting_cvd_svl                     false
% 2.27/1.02  --splitting_nvd                         32
% 2.27/1.02  --sub_typing                            true
% 2.27/1.02  --prep_gs_sim                           true
% 2.27/1.02  --prep_unflatten                        true
% 2.27/1.02  --prep_res_sim                          true
% 2.27/1.02  --prep_upred                            true
% 2.27/1.02  --prep_sem_filter                       exhaustive
% 2.27/1.02  --prep_sem_filter_out                   false
% 2.27/1.02  --pred_elim                             true
% 2.27/1.02  --res_sim_input                         true
% 2.27/1.02  --eq_ax_congr_red                       true
% 2.27/1.02  --pure_diseq_elim                       true
% 2.27/1.02  --brand_transform                       false
% 2.27/1.02  --non_eq_to_eq                          false
% 2.27/1.02  --prep_def_merge                        true
% 2.27/1.02  --prep_def_merge_prop_impl              false
% 2.27/1.02  --prep_def_merge_mbd                    true
% 2.27/1.02  --prep_def_merge_tr_red                 false
% 2.27/1.02  --prep_def_merge_tr_cl                  false
% 2.27/1.02  --smt_preprocessing                     true
% 2.27/1.02  --smt_ac_axioms                         fast
% 2.27/1.02  --preprocessed_out                      false
% 2.27/1.02  --preprocessed_stats                    false
% 2.27/1.02  
% 2.27/1.02  ------ Abstraction refinement Options
% 2.27/1.02  
% 2.27/1.02  --abstr_ref                             []
% 2.27/1.02  --abstr_ref_prep                        false
% 2.27/1.02  --abstr_ref_until_sat                   false
% 2.27/1.02  --abstr_ref_sig_restrict                funpre
% 2.27/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.02  --abstr_ref_under                       []
% 2.27/1.02  
% 2.27/1.02  ------ SAT Options
% 2.27/1.02  
% 2.27/1.02  --sat_mode                              false
% 2.27/1.02  --sat_fm_restart_options                ""
% 2.27/1.02  --sat_gr_def                            false
% 2.27/1.02  --sat_epr_types                         true
% 2.27/1.02  --sat_non_cyclic_types                  false
% 2.27/1.02  --sat_finite_models                     false
% 2.27/1.02  --sat_fm_lemmas                         false
% 2.27/1.02  --sat_fm_prep                           false
% 2.27/1.02  --sat_fm_uc_incr                        true
% 2.27/1.02  --sat_out_model                         small
% 2.27/1.02  --sat_out_clauses                       false
% 2.27/1.02  
% 2.27/1.02  ------ QBF Options
% 2.27/1.02  
% 2.27/1.02  --qbf_mode                              false
% 2.27/1.02  --qbf_elim_univ                         false
% 2.27/1.02  --qbf_dom_inst                          none
% 2.27/1.02  --qbf_dom_pre_inst                      false
% 2.27/1.02  --qbf_sk_in                             false
% 2.27/1.02  --qbf_pred_elim                         true
% 2.27/1.02  --qbf_split                             512
% 2.27/1.02  
% 2.27/1.02  ------ BMC1 Options
% 2.27/1.02  
% 2.27/1.02  --bmc1_incremental                      false
% 2.27/1.02  --bmc1_axioms                           reachable_all
% 2.27/1.02  --bmc1_min_bound                        0
% 2.27/1.02  --bmc1_max_bound                        -1
% 2.27/1.02  --bmc1_max_bound_default                -1
% 2.27/1.02  --bmc1_symbol_reachability              true
% 2.27/1.02  --bmc1_property_lemmas                  false
% 2.27/1.02  --bmc1_k_induction                      false
% 2.27/1.02  --bmc1_non_equiv_states                 false
% 2.27/1.02  --bmc1_deadlock                         false
% 2.27/1.02  --bmc1_ucm                              false
% 2.27/1.02  --bmc1_add_unsat_core                   none
% 2.27/1.02  --bmc1_unsat_core_children              false
% 2.27/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.02  --bmc1_out_stat                         full
% 2.27/1.02  --bmc1_ground_init                      false
% 2.27/1.02  --bmc1_pre_inst_next_state              false
% 2.27/1.02  --bmc1_pre_inst_state                   false
% 2.27/1.02  --bmc1_pre_inst_reach_state             false
% 2.27/1.02  --bmc1_out_unsat_core                   false
% 2.27/1.02  --bmc1_aig_witness_out                  false
% 2.27/1.02  --bmc1_verbose                          false
% 2.27/1.02  --bmc1_dump_clauses_tptp                false
% 2.27/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.02  --bmc1_dump_file                        -
% 2.27/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.02  --bmc1_ucm_extend_mode                  1
% 2.27/1.02  --bmc1_ucm_init_mode                    2
% 2.27/1.02  --bmc1_ucm_cone_mode                    none
% 2.27/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.02  --bmc1_ucm_relax_model                  4
% 2.27/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.02  --bmc1_ucm_layered_model                none
% 2.27/1.02  --bmc1_ucm_max_lemma_size               10
% 2.27/1.02  
% 2.27/1.02  ------ AIG Options
% 2.27/1.02  
% 2.27/1.02  --aig_mode                              false
% 2.27/1.02  
% 2.27/1.02  ------ Instantiation Options
% 2.27/1.02  
% 2.27/1.02  --instantiation_flag                    true
% 2.27/1.02  --inst_sos_flag                         false
% 2.27/1.02  --inst_sos_phase                        true
% 2.27/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.02  --inst_lit_sel_side                     none
% 2.27/1.02  --inst_solver_per_active                1400
% 2.27/1.02  --inst_solver_calls_frac                1.
% 2.27/1.02  --inst_passive_queue_type               priority_queues
% 2.27/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.02  --inst_passive_queues_freq              [25;2]
% 2.27/1.02  --inst_dismatching                      true
% 2.27/1.02  --inst_eager_unprocessed_to_passive     true
% 2.27/1.02  --inst_prop_sim_given                   true
% 2.27/1.02  --inst_prop_sim_new                     false
% 2.27/1.02  --inst_subs_new                         false
% 2.27/1.02  --inst_eq_res_simp                      false
% 2.27/1.02  --inst_subs_given                       false
% 2.27/1.02  --inst_orphan_elimination               true
% 2.27/1.02  --inst_learning_loop_flag               true
% 2.27/1.02  --inst_learning_start                   3000
% 2.27/1.02  --inst_learning_factor                  2
% 2.27/1.02  --inst_start_prop_sim_after_learn       3
% 2.27/1.02  --inst_sel_renew                        solver
% 2.27/1.02  --inst_lit_activity_flag                true
% 2.27/1.02  --inst_restr_to_given                   false
% 2.27/1.02  --inst_activity_threshold               500
% 2.27/1.02  --inst_out_proof                        true
% 2.27/1.02  
% 2.27/1.02  ------ Resolution Options
% 2.27/1.02  
% 2.27/1.02  --resolution_flag                       false
% 2.27/1.02  --res_lit_sel                           adaptive
% 2.27/1.02  --res_lit_sel_side                      none
% 2.27/1.02  --res_ordering                          kbo
% 2.27/1.02  --res_to_prop_solver                    active
% 2.27/1.02  --res_prop_simpl_new                    false
% 2.27/1.02  --res_prop_simpl_given                  true
% 2.27/1.02  --res_passive_queue_type                priority_queues
% 2.27/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.02  --res_passive_queues_freq               [15;5]
% 2.27/1.02  --res_forward_subs                      full
% 2.27/1.02  --res_backward_subs                     full
% 2.27/1.02  --res_forward_subs_resolution           true
% 2.27/1.02  --res_backward_subs_resolution          true
% 2.27/1.02  --res_orphan_elimination                true
% 2.27/1.02  --res_time_limit                        2.
% 2.27/1.02  --res_out_proof                         true
% 2.27/1.02  
% 2.27/1.02  ------ Superposition Options
% 2.27/1.02  
% 2.27/1.02  --superposition_flag                    true
% 2.27/1.02  --sup_passive_queue_type                priority_queues
% 2.27/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.02  --demod_completeness_check              fast
% 2.27/1.02  --demod_use_ground                      true
% 2.27/1.02  --sup_to_prop_solver                    passive
% 2.27/1.02  --sup_prop_simpl_new                    true
% 2.27/1.02  --sup_prop_simpl_given                  true
% 2.27/1.02  --sup_fun_splitting                     false
% 2.27/1.02  --sup_smt_interval                      50000
% 2.27/1.02  
% 2.27/1.02  ------ Superposition Simplification Setup
% 2.27/1.02  
% 2.27/1.02  --sup_indices_passive                   []
% 2.27/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.02  --sup_full_bw                           [BwDemod]
% 2.27/1.02  --sup_immed_triv                        [TrivRules]
% 2.27/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.02  --sup_immed_bw_main                     []
% 2.27/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.02  
% 2.27/1.02  ------ Combination Options
% 2.27/1.02  
% 2.27/1.02  --comb_res_mult                         3
% 2.27/1.02  --comb_sup_mult                         2
% 2.27/1.02  --comb_inst_mult                        10
% 2.27/1.02  
% 2.27/1.02  ------ Debug Options
% 2.27/1.02  
% 2.27/1.02  --dbg_backtrace                         false
% 2.27/1.02  --dbg_dump_prop_clauses                 false
% 2.27/1.02  --dbg_dump_prop_clauses_file            -
% 2.27/1.02  --dbg_out_stat                          false
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  ------ Proving...
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  % SZS status Theorem for theBenchmark.p
% 2.27/1.02  
% 2.27/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/1.02  
% 2.27/1.02  fof(f8,conjecture,(
% 2.27/1.02    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.02  
% 2.27/1.02  fof(f9,negated_conjecture,(
% 2.27/1.02    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.27/1.02    inference(negated_conjecture,[],[f8])).
% 2.27/1.02  
% 2.27/1.02  fof(f13,plain,(
% 2.27/1.02    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.27/1.02    inference(ennf_transformation,[],[f9])).
% 2.27/1.02  
% 2.27/1.02  fof(f14,plain,(
% 2.27/1.02    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.27/1.02    inference(flattening,[],[f13])).
% 2.27/1.02  
% 2.27/1.02  fof(f20,plain,(
% 2.27/1.02    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 2.27/1.02    introduced(choice_axiom,[])).
% 2.27/1.02  
% 2.27/1.02  fof(f21,plain,(
% 2.27/1.02    k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.27/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f20])).
% 2.27/1.02  
% 2.27/1.02  fof(f39,plain,(
% 2.27/1.02    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.27/1.02    inference(cnf_transformation,[],[f21])).
% 2.27/1.02  
% 2.27/1.02  fof(f4,axiom,(
% 2.27/1.02    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.02  
% 2.27/1.02  fof(f25,plain,(
% 2.27/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.27/1.02    inference(cnf_transformation,[],[f4])).
% 2.27/1.02  
% 2.27/1.02  fof(f2,axiom,(
% 2.27/1.02    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.02  
% 2.27/1.02  fof(f23,plain,(
% 2.27/1.02    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.27/1.02    inference(cnf_transformation,[],[f2])).
% 2.27/1.02  
% 2.27/1.02  fof(f47,plain,(
% 2.27/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.27/1.02    inference(definition_unfolding,[],[f25,f23])).
% 2.27/1.02  
% 2.27/1.02  fof(f62,plain,(
% 2.27/1.02    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.27/1.02    inference(definition_unfolding,[],[f39,f47])).
% 2.27/1.02  
% 2.27/1.02  fof(f5,axiom,(
% 2.27/1.02    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.02  
% 2.27/1.02  fof(f10,plain,(
% 2.27/1.02    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.27/1.02    inference(ennf_transformation,[],[f5])).
% 2.27/1.02  
% 2.27/1.02  fof(f18,plain,(
% 2.27/1.02    ( ! [X6,X7,X5] : (! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(X5,X6,X7,sK3(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)))) )),
% 2.27/1.02    introduced(choice_axiom,[])).
% 2.27/1.02  
% 2.27/1.02  fof(f17,plain,(
% 2.27/1.02    ( ! [X6,X5] : (! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)))) )),
% 2.27/1.02    introduced(choice_axiom,[])).
% 2.27/1.02  
% 2.27/1.02  fof(f16,plain,(
% 2.27/1.02    ( ! [X5] : (! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)))) )),
% 2.27/1.02    introduced(choice_axiom,[])).
% 2.27/1.02  
% 2.27/1.02  fof(f15,plain,(
% 2.27/1.02    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)))),
% 2.27/1.02    introduced(choice_axiom,[])).
% 2.27/1.02  
% 2.27/1.02  fof(f19,plain,(
% 2.27/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.27/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18,f17,f16,f15])).
% 2.27/1.02  
% 2.27/1.02  fof(f30,plain,(
% 2.27/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.02    inference(cnf_transformation,[],[f19])).
% 2.27/1.02  
% 2.27/1.02  fof(f3,axiom,(
% 2.27/1.02    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 2.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.02  
% 2.27/1.02  fof(f24,plain,(
% 2.27/1.02    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 2.27/1.02    inference(cnf_transformation,[],[f3])).
% 2.27/1.02  
% 2.27/1.02  fof(f1,axiom,(
% 2.27/1.02    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.02  
% 2.27/1.02  fof(f22,plain,(
% 2.27/1.02    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.27/1.02    inference(cnf_transformation,[],[f1])).
% 2.27/1.02  
% 2.27/1.02  fof(f46,plain,(
% 2.27/1.02    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 2.27/1.02    inference(definition_unfolding,[],[f24,f22])).
% 2.27/1.02  
% 2.27/1.02  fof(f48,plain,(
% 2.27/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.02    inference(definition_unfolding,[],[f30,f46,f47])).
% 2.27/1.02  
% 2.27/1.02  fof(f41,plain,(
% 2.27/1.02    k1_xboole_0 != sK4),
% 2.27/1.02    inference(cnf_transformation,[],[f21])).
% 2.27/1.02  
% 2.27/1.02  fof(f42,plain,(
% 2.27/1.02    k1_xboole_0 != sK5),
% 2.27/1.02    inference(cnf_transformation,[],[f21])).
% 2.27/1.03  
% 2.27/1.03  fof(f43,plain,(
% 2.27/1.03    k1_xboole_0 != sK6),
% 2.27/1.03    inference(cnf_transformation,[],[f21])).
% 2.27/1.03  
% 2.27/1.03  fof(f44,plain,(
% 2.27/1.03    k1_xboole_0 != sK7),
% 2.27/1.03    inference(cnf_transformation,[],[f21])).
% 2.27/1.03  
% 2.27/1.03  fof(f40,plain,(
% 2.27/1.03    ( ! [X6,X8,X7,X9] : (sK8 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f21])).
% 2.27/1.03  
% 2.27/1.03  fof(f61,plain,(
% 2.27/1.03    ( ! [X6,X8,X7,X9] : (sK8 = X9 | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 2.27/1.03    inference(definition_unfolding,[],[f40,f46])).
% 2.27/1.03  
% 2.27/1.03  fof(f26,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f19])).
% 2.27/1.03  
% 2.27/1.03  fof(f52,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f26,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f27,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f19])).
% 2.27/1.03  
% 2.27/1.03  fof(f51,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f27,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f28,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f19])).
% 2.27/1.03  
% 2.27/1.03  fof(f50,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f28,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f29,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f19])).
% 2.27/1.03  
% 2.27/1.03  fof(f49,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f29,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f6,axiom,(
% 2.27/1.03    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.27/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f11,plain,(
% 2.27/1.03    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.27/1.03    inference(ennf_transformation,[],[f6])).
% 2.27/1.03  
% 2.27/1.03  fof(f31,plain,(
% 2.27/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f11])).
% 2.27/1.03  
% 2.27/1.03  fof(f56,plain,(
% 2.27/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f31,f46,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f66,plain,(
% 2.27/1.03    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(equality_resolution,[],[f56])).
% 2.27/1.03  
% 2.27/1.03  fof(f7,axiom,(
% 2.27/1.03    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.27/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f12,plain,(
% 2.27/1.03    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.27/1.03    inference(ennf_transformation,[],[f7])).
% 2.27/1.03  
% 2.27/1.03  fof(f35,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f12])).
% 2.27/1.03  
% 2.27/1.03  fof(f60,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f35,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f32,plain,(
% 2.27/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f11])).
% 2.27/1.03  
% 2.27/1.03  fof(f55,plain,(
% 2.27/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f32,f46,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f65,plain,(
% 2.27/1.03    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(equality_resolution,[],[f55])).
% 2.27/1.03  
% 2.27/1.03  fof(f36,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f12])).
% 2.27/1.03  
% 2.27/1.03  fof(f59,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f36,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f34,plain,(
% 2.27/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f11])).
% 2.27/1.03  
% 2.27/1.03  fof(f53,plain,(
% 2.27/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f34,f46,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f63,plain,(
% 2.27/1.03    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(equality_resolution,[],[f53])).
% 2.27/1.03  
% 2.27/1.03  fof(f38,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f12])).
% 2.27/1.03  
% 2.27/1.03  fof(f57,plain,(
% 2.27/1.03    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.27/1.03    inference(definition_unfolding,[],[f38,f47])).
% 2.27/1.03  
% 2.27/1.03  fof(f45,plain,(
% 2.27/1.03    k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8),
% 2.27/1.03    inference(cnf_transformation,[],[f21])).
% 2.27/1.03  
% 2.27/1.03  cnf(c_19,negated_conjecture,
% 2.27/1.03      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 2.27/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_426,plain,
% 2.27/1.03      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_0,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)),sK3(X1,X2,X3,X4,X0)) = X0
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_440,plain,
% 2.27/1.03      ( k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3554,plain,
% 2.27/1.03      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_440]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_17,negated_conjecture,
% 2.27/1.03      ( k1_xboole_0 != sK4 ),
% 2.27/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_16,negated_conjecture,
% 2.27/1.03      ( k1_xboole_0 != sK5 ),
% 2.27/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_15,negated_conjecture,
% 2.27/1.03      ( k1_xboole_0 != sK6 ),
% 2.27/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_14,negated_conjecture,
% 2.27/1.03      ( k1_xboole_0 != sK7 ),
% 2.27/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_181,plain,( X0 = X0 ),theory(equality) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_202,plain,
% 2.27/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_181]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_182,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_656,plain,
% 2.27/1.03      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_182]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_657,plain,
% 2.27/1.03      ( sK7 != k1_xboole_0
% 2.27/1.03      | k1_xboole_0 = sK7
% 2.27/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_656]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_658,plain,
% 2.27/1.03      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_182]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_659,plain,
% 2.27/1.03      ( sK6 != k1_xboole_0
% 2.27/1.03      | k1_xboole_0 = sK6
% 2.27/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_658]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_660,plain,
% 2.27/1.03      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_182]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_661,plain,
% 2.27/1.03      ( sK5 != k1_xboole_0
% 2.27/1.03      | k1_xboole_0 = sK5
% 2.27/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_660]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_662,plain,
% 2.27/1.03      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_182]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_663,plain,
% 2.27/1.03      ( sK4 != k1_xboole_0
% 2.27/1.03      | k1_xboole_0 = sK4
% 2.27/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/1.03      inference(instantiation,[status(thm)],[c_662]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3555,plain,
% 2.27/1.03      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9 ),
% 2.27/1.03      inference(global_propositional_subsumption,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_3554,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,
% 2.27/1.03                 c_663]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_18,negated_conjecture,
% 2.27/1.03      ( ~ m1_subset_1(X0,sK7)
% 2.27/1.03      | ~ m1_subset_1(X1,sK6)
% 2.27/1.03      | ~ m1_subset_1(X2,sK5)
% 2.27/1.03      | ~ m1_subset_1(X3,sK4)
% 2.27/1.03      | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK9
% 2.27/1.03      | sK8 = X0 ),
% 2.27/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_427,plain,
% 2.27/1.03      ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK9
% 2.27/1.03      | sK8 = X3
% 2.27/1.03      | m1_subset_1(X3,sK7) != iProver_top
% 2.27/1.03      | m1_subset_1(X2,sK6) != iProver_top
% 2.27/1.03      | m1_subset_1(X1,sK5) != iProver_top
% 2.27/1.03      | m1_subset_1(X0,sK4) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3560,plain,
% 2.27/1.03      ( sK3(sK4,sK5,sK6,sK7,sK9) = sK8
% 2.27/1.03      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) != iProver_top
% 2.27/1.03      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) != iProver_top
% 2.27/1.03      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) != iProver_top
% 2.27/1.03      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) != iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_3555,c_427]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_4,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_436,plain,
% 2.27/1.03      ( k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.27/1.03      | m1_subset_1(sK0(X2,X1,X0,X3,X4),X2) = iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_1336,plain,
% 2.27/1.03      ( sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0
% 2.27/1.03      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) = iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_436]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_437,plain,
% 2.27/1.03      ( k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.27/1.03      | m1_subset_1(sK1(X2,X1,X0,X3,X4),X1) = iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_1345,plain,
% 2.27/1.03      ( sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0
% 2.27/1.03      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) = iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_437]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_2,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_438,plain,
% 2.27/1.03      ( k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.27/1.03      | m1_subset_1(sK2(X2,X1,X0,X3,X4),X0) = iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_1494,plain,
% 2.27/1.03      ( sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0
% 2.27/1.03      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) = iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_438]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_1,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | m1_subset_1(sK3(X1,X2,X3,X4,X0),X4)
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_439,plain,
% 2.27/1.03      ( k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.27/1.03      | m1_subset_1(sK3(X2,X1,X0,X3,X4),X3) = iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_2452,plain,
% 2.27/1.03      ( sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0
% 2.27/1.03      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) = iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_439]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3783,plain,
% 2.27/1.03      ( sK3(sK4,sK5,sK6,sK7,sK9) = sK8 ),
% 2.27/1.03      inference(global_propositional_subsumption,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_3560,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,
% 2.27/1.03                 c_663,c_1336,c_1345,c_1494,c_2452]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3786,plain,
% 2.27/1.03      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK8) = sK9 ),
% 2.27/1.03      inference(demodulation,[status(thm)],[c_3783,c_3555]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_8,plain,
% 2.27/1.03      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
% 2.27/1.03      | k8_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X0
% 2.27/1.03      | k1_xboole_0 = X7
% 2.27/1.03      | k1_xboole_0 = X6
% 2.27/1.03      | k1_xboole_0 = X5
% 2.27/1.03      | k1_xboole_0 = X4 ),
% 2.27/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_432,plain,
% 2.27/1.03      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3572,plain,
% 2.27/1.03      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9))) = sK0(sK4,sK5,sK6,sK7,sK9)
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_3555,c_432]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3579,plain,
% 2.27/1.03      ( k8_mcart_1(X0,X1,X2,X3,sK9) = sK0(sK4,sK5,sK6,sK7,sK9)
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(light_normalisation,[status(thm)],[c_3572,c_3555]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3855,plain,
% 2.27/1.03      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK0(sK4,sK5,sK6,sK7,sK9)
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_3579]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_12,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_428,plain,
% 2.27/1.03      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_1180,plain,
% 2.27/1.03      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_428]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_2238,plain,
% 2.27/1.03      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 2.27/1.03      inference(global_propositional_subsumption,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_1180,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,
% 2.27/1.03                 c_663]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3856,plain,
% 2.27/1.03      ( sK0(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(light_normalisation,[status(thm)],[c_3855,c_2238]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3857,plain,
% 2.27/1.03      ( sK0(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 2.27/1.03      inference(global_propositional_subsumption,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_3856,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,
% 2.27/1.03                 c_663]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_7,plain,
% 2.27/1.03      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
% 2.27/1.03      | k9_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X1
% 2.27/1.03      | k1_xboole_0 = X7
% 2.27/1.03      | k1_xboole_0 = X6
% 2.27/1.03      | k1_xboole_0 = X5
% 2.27/1.03      | k1_xboole_0 = X4 ),
% 2.27/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_433,plain,
% 2.27/1.03      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3571,plain,
% 2.27/1.03      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9)),sK2(sK4,sK5,sK6,sK7,sK9)),sK3(sK4,sK5,sK6,sK7,sK9))) = sK1(sK4,sK5,sK6,sK7,sK9)
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_3555,c_433]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3592,plain,
% 2.27/1.03      ( k9_mcart_1(X0,X1,X2,X3,sK9) = sK1(sK4,sK5,sK6,sK7,sK9)
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(light_normalisation,[status(thm)],[c_3571,c_3555]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3945,plain,
% 2.27/1.03      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK1(sK4,sK5,sK6,sK7,sK9)
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_3592]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_11,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_429,plain,
% 2.27/1.03      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_2461,plain,
% 2.27/1.03      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_429]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3140,plain,
% 2.27/1.03      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 2.27/1.03      inference(global_propositional_subsumption,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_2461,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,
% 2.27/1.03                 c_663]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3946,plain,
% 2.27/1.03      ( sK1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(light_normalisation,[status(thm)],[c_3945,c_3140]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3947,plain,
% 2.27/1.03      ( sK1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 2.27/1.03      inference(global_propositional_subsumption,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_3946,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,
% 2.27/1.03                 c_663]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3965,plain,
% 2.27/1.03      ( k4_tarski(k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))),sK2(sK4,sK5,sK6,sK7,sK9)),sK8) = sK9 ),
% 2.27/1.03      inference(light_normalisation,[status(thm)],[c_3786,c_3857,c_3947]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_5,plain,
% 2.27/1.03      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
% 2.27/1.03      | k11_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X3
% 2.27/1.03      | k1_xboole_0 = X7
% 2.27/1.03      | k1_xboole_0 = X6
% 2.27/1.03      | k1_xboole_0 = X5
% 2.27/1.03      | k1_xboole_0 = X4 ),
% 2.27/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_435,plain,
% 2.27/1.03      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_3978,plain,
% 2.27/1.03      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))),sK2(sK4,sK5,sK6,sK7,sK9)),sK8)) = sK8
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_3965,c_435]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_4009,plain,
% 2.27/1.03      ( k11_mcart_1(X0,X1,X2,X3,sK9) = sK8
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(light_normalisation,[status(thm)],[c_3978,c_3965]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_4242,plain,
% 2.27/1.03      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_4009]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_9,plain,
% 2.27/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.27/1.03      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 2.27/1.03      | k1_xboole_0 = X4
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1 ),
% 2.27/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_431,plain,
% 2.27/1.03      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 2.27/1.03      | k1_xboole_0 = X2
% 2.27/1.03      | k1_xboole_0 = X1
% 2.27/1.03      | k1_xboole_0 = X0
% 2.27/1.03      | k1_xboole_0 = X3
% 2.27/1.03      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.27/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_970,plain,
% 2.27/1.03      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9)
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(superposition,[status(thm)],[c_426,c_431]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_1496,plain,
% 2.27/1.03      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(sK9) ),
% 2.27/1.03      inference(global_propositional_subsumption,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_970,c_17,c_16,c_15,c_14,c_202,c_657,c_659,c_661,c_663]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_4243,plain,
% 2.27/1.03      ( k2_mcart_1(sK9) = sK8
% 2.27/1.03      | sK7 = k1_xboole_0
% 2.27/1.03      | sK6 = k1_xboole_0
% 2.27/1.03      | sK5 = k1_xboole_0
% 2.27/1.03      | sK4 = k1_xboole_0 ),
% 2.27/1.03      inference(demodulation,[status(thm)],[c_4242,c_1496]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_13,negated_conjecture,
% 2.27/1.03      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
% 2.27/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(c_1499,plain,
% 2.27/1.03      ( k2_mcart_1(sK9) != sK8 ),
% 2.27/1.03      inference(demodulation,[status(thm)],[c_1496,c_13]) ).
% 2.27/1.03  
% 2.27/1.03  cnf(contradiction,plain,
% 2.27/1.03      ( $false ),
% 2.27/1.03      inference(minisat,
% 2.27/1.03                [status(thm)],
% 2.27/1.03                [c_4243,c_1499,c_663,c_661,c_659,c_657,c_202,c_14,c_15,
% 2.27/1.03                 c_16,c_17]) ).
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.03  
% 2.27/1.03  ------                               Statistics
% 2.27/1.03  
% 2.27/1.03  ------ General
% 2.27/1.03  
% 2.27/1.03  abstr_ref_over_cycles:                  0
% 2.27/1.03  abstr_ref_under_cycles:                 0
% 2.27/1.03  gc_basic_clause_elim:                   0
% 2.27/1.03  forced_gc_time:                         0
% 2.27/1.03  parsing_time:                           0.009
% 2.27/1.03  unif_index_cands_time:                  0.
% 2.27/1.03  unif_index_add_time:                    0.
% 2.27/1.03  orderings_time:                         0.
% 2.27/1.03  out_proof_time:                         0.017
% 2.27/1.03  total_time:                             0.24
% 2.27/1.03  num_of_symbols:                         51
% 2.27/1.03  num_of_terms:                           11066
% 2.27/1.03  
% 2.27/1.03  ------ Preprocessing
% 2.27/1.03  
% 2.27/1.03  num_of_splits:                          0
% 2.27/1.03  num_of_split_atoms:                     0
% 2.27/1.03  num_of_reused_defs:                     0
% 2.27/1.03  num_eq_ax_congr_red:                    64
% 2.27/1.03  num_of_sem_filtered_clauses:            1
% 2.27/1.03  num_of_subtypes:                        0
% 2.27/1.03  monotx_restored_types:                  0
% 2.27/1.03  sat_num_of_epr_types:                   0
% 2.27/1.03  sat_num_of_non_cyclic_types:            0
% 2.27/1.03  sat_guarded_non_collapsed_types:        0
% 2.27/1.03  num_pure_diseq_elim:                    0
% 2.27/1.03  simp_replaced_by:                       0
% 2.27/1.03  res_preprocessed:                       83
% 2.27/1.03  prep_upred:                             0
% 2.27/1.03  prep_unflattend:                        0
% 2.27/1.03  smt_new_axioms:                         0
% 2.27/1.03  pred_elim_cands:                        1
% 2.27/1.03  pred_elim:                              0
% 2.27/1.03  pred_elim_cl:                           0
% 2.27/1.03  pred_elim_cycles:                       1
% 2.27/1.03  merged_defs:                            0
% 2.27/1.03  merged_defs_ncl:                        0
% 2.27/1.03  bin_hyper_res:                          0
% 2.27/1.03  prep_cycles:                            3
% 2.27/1.03  pred_elim_time:                         0.
% 2.27/1.03  splitting_time:                         0.
% 2.27/1.03  sem_filter_time:                        0.
% 2.27/1.03  monotx_time:                            0.
% 2.27/1.03  subtype_inf_time:                       0.
% 2.27/1.03  
% 2.27/1.03  ------ Problem properties
% 2.27/1.03  
% 2.27/1.03  clauses:                                20
% 2.27/1.03  conjectures:                            7
% 2.27/1.03  epr:                                    4
% 2.27/1.03  horn:                                   7
% 2.27/1.03  ground:                                 6
% 2.27/1.03  unary:                                  6
% 2.27/1.03  binary:                                 0
% 2.27/1.03  lits:                                   90
% 2.27/1.03  lits_eq:                                68
% 2.27/1.03  fd_pure:                                0
% 2.27/1.03  fd_pseudo:                              0
% 2.27/1.03  fd_cond:                                9
% 2.27/1.03  fd_pseudo_cond:                         0
% 2.27/1.03  ac_symbols:                             0
% 2.27/1.03  
% 2.27/1.03  ------ Propositional Solver
% 2.27/1.03  
% 2.27/1.03  prop_solver_calls:                      22
% 2.27/1.03  prop_fast_solver_calls:                 909
% 2.27/1.03  smt_solver_calls:                       0
% 2.27/1.03  smt_fast_solver_calls:                  0
% 2.27/1.03  prop_num_of_clauses:                    1771
% 2.27/1.03  prop_preprocess_simplified:             6689
% 2.27/1.03  prop_fo_subsumed:                       52
% 2.27/1.03  prop_solver_time:                       0.
% 2.27/1.03  smt_solver_time:                        0.
% 2.27/1.03  smt_fast_solver_time:                   0.
% 2.27/1.03  prop_fast_solver_time:                  0.
% 2.27/1.03  prop_unsat_core_time:                   0.
% 2.27/1.03  
% 2.27/1.03  ------ QBF
% 2.27/1.03  
% 2.27/1.03  qbf_q_res:                              0
% 2.27/1.03  qbf_num_tautologies:                    0
% 2.27/1.03  qbf_prep_cycles:                        0
% 2.27/1.03  
% 2.27/1.03  ------ BMC1
% 2.27/1.03  
% 2.27/1.03  bmc1_current_bound:                     -1
% 2.27/1.03  bmc1_last_solved_bound:                 -1
% 2.27/1.03  bmc1_unsat_core_size:                   -1
% 2.27/1.03  bmc1_unsat_core_parents_size:           -1
% 2.27/1.03  bmc1_merge_next_fun:                    0
% 2.27/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.03  
% 2.27/1.03  ------ Instantiation
% 2.27/1.03  
% 2.27/1.03  inst_num_of_clauses:                    567
% 2.27/1.03  inst_num_in_passive:                    302
% 2.27/1.03  inst_num_in_active:                     240
% 2.27/1.03  inst_num_in_unprocessed:                25
% 2.27/1.03  inst_num_of_loops:                      240
% 2.27/1.03  inst_num_of_learning_restarts:          0
% 2.27/1.03  inst_num_moves_active_passive:          0
% 2.27/1.03  inst_lit_activity:                      0
% 2.27/1.03  inst_lit_activity_moves:                0
% 2.27/1.03  inst_num_tautologies:                   0
% 2.27/1.03  inst_num_prop_implied:                  0
% 2.27/1.03  inst_num_existing_simplified:           0
% 2.27/1.03  inst_num_eq_res_simplified:             0
% 2.27/1.03  inst_num_child_elim:                    0
% 2.27/1.03  inst_num_of_dismatching_blockings:      0
% 2.27/1.03  inst_num_of_non_proper_insts:           525
% 2.27/1.03  inst_num_of_duplicates:                 0
% 2.27/1.03  inst_inst_num_from_inst_to_res:         0
% 2.27/1.03  inst_dismatching_checking_time:         0.
% 2.27/1.03  
% 2.27/1.03  ------ Resolution
% 2.27/1.03  
% 2.27/1.03  res_num_of_clauses:                     0
% 2.27/1.03  res_num_in_passive:                     0
% 2.27/1.03  res_num_in_active:                      0
% 2.27/1.03  res_num_of_loops:                       86
% 2.27/1.03  res_forward_subset_subsumed:            5
% 2.27/1.03  res_backward_subset_subsumed:           0
% 2.27/1.03  res_forward_subsumed:                   0
% 2.27/1.03  res_backward_subsumed:                  0
% 2.27/1.03  res_forward_subsumption_resolution:     0
% 2.27/1.03  res_backward_subsumption_resolution:    0
% 2.27/1.03  res_clause_to_clause_subsumption:       61
% 2.27/1.03  res_orphan_elimination:                 0
% 2.27/1.03  res_tautology_del:                      0
% 2.27/1.03  res_num_eq_res_simplified:              0
% 2.27/1.03  res_num_sel_changes:                    0
% 2.27/1.03  res_moves_from_active_to_pass:          0
% 2.27/1.03  
% 2.27/1.03  ------ Superposition
% 2.27/1.03  
% 2.27/1.03  sup_time_total:                         0.
% 2.27/1.03  sup_time_generating:                    0.
% 2.27/1.03  sup_time_sim_full:                      0.
% 2.27/1.03  sup_time_sim_immed:                     0.
% 2.27/1.03  
% 2.27/1.03  sup_num_of_clauses:                     52
% 2.27/1.03  sup_num_in_active:                      34
% 2.27/1.03  sup_num_in_passive:                     18
% 2.27/1.03  sup_num_of_loops:                       47
% 2.27/1.03  sup_fw_superposition:                   13
% 2.27/1.03  sup_bw_superposition:                   30
% 2.27/1.03  sup_immediate_simplified:               31
% 2.27/1.03  sup_given_eliminated:                   0
% 2.27/1.03  comparisons_done:                       0
% 2.27/1.03  comparisons_avoided:                    28
% 2.27/1.03  
% 2.27/1.03  ------ Simplifications
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  sim_fw_subset_subsumed:                 0
% 2.27/1.03  sim_bw_subset_subsumed:                 0
% 2.27/1.03  sim_fw_subsumed:                        3
% 2.27/1.03  sim_bw_subsumed:                        0
% 2.27/1.03  sim_fw_subsumption_res:                 0
% 2.27/1.03  sim_bw_subsumption_res:                 0
% 2.27/1.03  sim_tautology_del:                      0
% 2.27/1.03  sim_eq_tautology_del:                   1
% 2.27/1.03  sim_eq_res_simp:                        0
% 2.27/1.03  sim_fw_demodulated:                     1
% 2.27/1.03  sim_bw_demodulated:                     14
% 2.27/1.03  sim_light_normalised:                   31
% 2.27/1.03  sim_joinable_taut:                      0
% 2.27/1.03  sim_joinable_simp:                      0
% 2.27/1.03  sim_ac_normalised:                      0
% 2.27/1.03  sim_smt_subsumption:                    0
% 2.27/1.03  
%------------------------------------------------------------------------------
