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
% DateTime   : Thu Dec  3 11:59:19 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  103 (1362 expanded)
%              Number of clauses        :   67 ( 494 expanded)
%              Number of leaves         :   12 ( 393 expanded)
%              Depth                    :   27
%              Number of atoms          :  539 (11276 expanded)
%              Number of equality atoms :  422 (6954 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f20,plain,
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
   => ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12
      & k1_xboole_0 != sK11
      & k1_xboole_0 != sK10
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK12 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != sK13
                      | ~ m1_subset_1(X9,sK11) )
                  | ~ m1_subset_1(X8,sK10) )
              | ~ m1_subset_1(X7,sK9) )
          | ~ m1_subset_1(X6,sK8) )
      & m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12
    & k1_xboole_0 != sK11
    & k1_xboole_0 != sK10
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK12 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != sK13
                    | ~ m1_subset_1(X9,sK11) )
                | ~ m1_subset_1(X8,sK10) )
            | ~ m1_subset_1(X7,sK9) )
        | ~ m1_subset_1(X6,sK8) )
    & m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12,sK13])],[f10,f20])).

fof(f34,plain,(
    m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
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

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(X5,X6,X7,X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(X5,X6,X7,sK7(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(X5,X6,X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(X5,X6,sK6(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X2) ) ) ),
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
                ( k4_mcart_1(X5,sK5(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X1) ) ) ),
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
                    ( k4_mcart_1(sK4(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK4(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK7(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK5(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK4(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f7,f18,f17,f16,f15])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X6 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK0(X4,X5) != X5
        & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK0(X4,X5) != X5
                    & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X6,X8,X7,X9] :
      ( sK12 = X6
      | k4_mcart_1(X6,X7,X8,X9) != sK13
      | ~ m1_subset_1(X9,sK11)
      | ~ m1_subset_1(X8,sK10)
      | ~ m1_subset_1(X7,sK9)
      | ~ m1_subset_1(X6,sK8) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12 ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X4
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | sK0(X4,X5) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_291,plain,
    ( m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK4(X1,X2,X3,X4,X0),X1)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_293,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
    | m1_subset_1(sK4(X2,X1,X0,X3,X4),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k4_zfmisc_1(X1,X3,X4,X5))
    | k8_mcart_1(X1,X3,X4,X5,X2) = X0
    | k4_mcart_1(sK0(X2,X0),sK1(X2,X0),sK2(X2,X0),sK3(X2,X0)) = X2
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_299,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3081,plain,
    ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = X0
    | k4_mcart_1(sK0(sK13,X0),sK1(sK13,X0),sK2(sK13,X0),sK3(sK13,X0)) = sK13
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_291,c_299])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_126,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_137,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_127,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_470,plain,
    ( sK11 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_471,plain,
    ( sK11 != k1_xboole_0
    | k1_xboole_0 = sK11
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_472,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_473,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_474,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_475,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_476,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_477,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_3204,plain,
    ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = X0
    | k4_mcart_1(sK0(sK13,X0),sK1(sK13,X0),sK2(sK13,X0),sK3(sK13,X0)) = sK13
    | m1_subset_1(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3081,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,c_477])).

cnf(c_3213,plain,
    ( sK4(sK8,X0,X1,X2,X3) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
    | k4_mcart_1(sK0(sK13,sK4(sK8,X0,X1,X2,X3)),sK1(sK13,sK4(sK8,X0,X1,X2,X3)),sK2(sK13,sK4(sK8,X0,X1,X2,X3)),sK3(sK13,sK4(sK8,X0,X1,X2,X3))) = sK13
    | sK8 = k1_xboole_0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k4_zfmisc_1(sK8,X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_293,c_3204])).

cnf(c_3857,plain,
    ( k4_mcart_1(sK0(sK13,sK4(sK8,X0,X1,X2,X3)),sK1(sK13,sK4(sK8,X0,X1,X2,X3)),sK2(sK13,sK4(sK8,X0,X1,X2,X3)),sK3(sK13,sK4(sK8,X0,X1,X2,X3))) = sK13
    | sK4(sK8,X0,X1,X2,X3) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k4_zfmisc_1(sK8,X0,X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3213,c_16,c_137,c_477])).

cnf(c_3858,plain,
    ( sK4(sK8,X0,X1,X2,X3) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
    | k4_mcart_1(sK0(sK13,sK4(sK8,X0,X1,X2,X3)),sK1(sK13,sK4(sK8,X0,X1,X2,X3)),sK2(sK13,sK4(sK8,X0,X1,X2,X3)),sK3(sK13,sK4(sK8,X0,X1,X2,X3))) = sK13
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k4_zfmisc_1(sK8,X0,X1,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3857])).

cnf(c_3867,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
    | k4_mcart_1(sK0(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK1(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK2(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK3(sK13,sK4(sK8,sK9,sK10,sK11,sK13))) = sK13
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_291,c_3858])).

cnf(c_4999,plain,
    ( k4_mcart_1(sK0(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK1(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK2(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK3(sK13,sK4(sK8,sK9,sK10,sK11,sK13))) = sK13
    | sK4(sK8,sK9,sK10,sK11,sK13) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3867,c_15,c_14,c_13,c_137,c_471,c_473,c_475])).

cnf(c_5000,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
    | k4_mcart_1(sK0(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK1(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK2(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK3(sK13,sK4(sK8,sK9,sK10,sK11,sK13))) = sK13 ),
    inference(renaming,[status(thm)],[c_4999])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK5(X1,X2,X3,X4,X0),X2)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_294,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
    | m1_subset_1(sK5(X2,X1,X0,X3,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK6(X1,X2,X3,X4,X0),X3)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_295,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
    | m1_subset_1(sK6(X2,X1,X0,X3,X4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK7(X1,X2,X3,X4,X0),X4)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_296,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
    | m1_subset_1(sK7(X2,X1,X0,X3,X4),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k4_mcart_1(sK4(X1,X2,X3,X4,X0),sK5(X1,X2,X3,X4,X0),sK6(X1,X2,X3,X4,X0),sK7(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_297,plain,
    ( k4_mcart_1(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1589,plain,
    ( k4_mcart_1(sK4(sK8,sK9,sK10,sK11,sK13),sK5(sK8,sK9,sK10,sK11,sK13),sK6(sK8,sK9,sK10,sK11,sK13),sK7(sK8,sK9,sK10,sK11,sK13)) = sK13
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_291,c_297])).

cnf(c_1688,plain,
    ( k4_mcart_1(sK4(sK8,sK9,sK10,sK11,sK13),sK5(sK8,sK9,sK10,sK11,sK13),sK6(sK8,sK9,sK10,sK11,sK13),sK7(sK8,sK9,sK10,sK11,sK13)) = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1589,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,c_477])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK11)
    | ~ m1_subset_1(X1,sK10)
    | ~ m1_subset_1(X2,sK9)
    | ~ m1_subset_1(X3,sK8)
    | k4_mcart_1(X3,X2,X1,X0) != sK13
    | sK12 = X3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_292,plain,
    ( k4_mcart_1(X0,X1,X2,X3) != sK13
    | sK12 = X0
    | m1_subset_1(X3,sK11) != iProver_top
    | m1_subset_1(X2,sK10) != iProver_top
    | m1_subset_1(X1,sK9) != iProver_top
    | m1_subset_1(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1691,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | m1_subset_1(sK7(sK8,sK9,sK10,sK11,sK13),sK11) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_292])).

cnf(c_2004,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
    | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_296,c_1691])).

cnf(c_19,plain,
    ( m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3556,plain,
    ( m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
    | sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2004,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,c_477])).

cnf(c_3557,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_3556])).

cnf(c_3564,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
    | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_295,c_3557])).

cnf(c_4388,plain,
    ( m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
    | sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3564,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,c_477])).

cnf(c_4389,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_4388])).

cnf(c_4395,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
    | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_294,c_4389])).

cnf(c_4398,plain,
    ( m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
    | sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4395,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,c_477])).

cnf(c_4399,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_4398])).

cnf(c_4404,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_293,c_4399])).

cnf(c_4677,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4404,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,c_477])).

cnf(c_5001,plain,
    ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = sK12
    | k4_mcart_1(sK0(sK13,sK12),sK1(sK13,sK12),sK2(sK13,sK12),sK3(sK13,sK12)) = sK13 ),
    inference(light_normalisation,[status(thm)],[c_5000,c_4677])).

cnf(c_12,negated_conjecture,
    ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5004,plain,
    ( k4_mcart_1(sK0(sK13,sK12),sK1(sK13,sK12),sK2(sK13,sK12),sK3(sK13,sK12)) = sK13 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5001,c_12])).

cnf(c_11,plain,
    ( X0 = X1
    | k4_mcart_1(X0,X2,X3,X4) != k4_mcart_1(X1,X5,X6,X7) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1698,plain,
    ( sK4(sK8,sK9,sK10,sK11,sK13) = X0
    | k4_mcart_1(X0,X1,X2,X3) != sK13 ),
    inference(superposition,[status(thm)],[c_1688,c_11])).

cnf(c_4681,plain,
    ( k4_mcart_1(X0,X1,X2,X3) != sK13
    | sK12 = X0 ),
    inference(demodulation,[status(thm)],[c_4677,c_1698])).

cnf(c_5006,plain,
    ( sK0(sK13,sK12) = sK12 ),
    inference(superposition,[status(thm)],[c_5004,c_4681])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k4_zfmisc_1(X1,X3,X4,X5))
    | k8_mcart_1(X1,X3,X4,X5,X2) = X0
    | sK0(X2,X0) != X0
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_300,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | sK0(X4,X5) != X5
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5049,plain,
    ( k8_mcart_1(X0,X1,X2,X3,sK13) = sK12
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK12,X0) != iProver_top
    | m1_subset_1(sK13,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5006,c_300])).

cnf(c_6221,plain,
    ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = sK12
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK12,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_291,c_5049])).

cnf(c_4705,plain,
    ( sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK12,sK8) = iProver_top
    | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4677,c_293])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6221,c_4705,c_477,c_475,c_473,c_471,c_137,c_12,c_13,c_14,c_15,c_16,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:40:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.62/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/0.97  
% 2.62/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/0.97  
% 2.62/0.97  ------  iProver source info
% 2.62/0.97  
% 2.62/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.62/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/0.97  git: non_committed_changes: false
% 2.62/0.97  git: last_make_outside_of_git: false
% 2.62/0.97  
% 2.62/0.97  ------ 
% 2.62/0.97  
% 2.62/0.97  ------ Input Options
% 2.62/0.97  
% 2.62/0.97  --out_options                           all
% 2.62/0.97  --tptp_safe_out                         true
% 2.62/0.97  --problem_path                          ""
% 2.62/0.97  --include_path                          ""
% 2.62/0.97  --clausifier                            res/vclausify_rel
% 2.62/0.97  --clausifier_options                    --mode clausify
% 2.62/0.97  --stdin                                 false
% 2.62/0.97  --stats_out                             all
% 2.62/0.97  
% 2.62/0.97  ------ General Options
% 2.62/0.97  
% 2.62/0.97  --fof                                   false
% 2.62/0.97  --time_out_real                         305.
% 2.62/0.97  --time_out_virtual                      -1.
% 2.62/0.97  --symbol_type_check                     false
% 2.62/0.97  --clausify_out                          false
% 2.62/0.97  --sig_cnt_out                           false
% 2.62/0.97  --trig_cnt_out                          false
% 2.62/0.97  --trig_cnt_out_tolerance                1.
% 2.62/0.97  --trig_cnt_out_sk_spl                   false
% 2.62/0.97  --abstr_cl_out                          false
% 2.62/0.97  
% 2.62/0.97  ------ Global Options
% 2.62/0.97  
% 2.62/0.97  --schedule                              default
% 2.62/0.97  --add_important_lit                     false
% 2.62/0.97  --prop_solver_per_cl                    1000
% 2.62/0.97  --min_unsat_core                        false
% 2.62/0.97  --soft_assumptions                      false
% 2.62/0.97  --soft_lemma_size                       3
% 2.62/0.97  --prop_impl_unit_size                   0
% 2.62/0.97  --prop_impl_unit                        []
% 2.62/0.97  --share_sel_clauses                     true
% 2.62/0.97  --reset_solvers                         false
% 2.62/0.97  --bc_imp_inh                            [conj_cone]
% 2.62/0.97  --conj_cone_tolerance                   3.
% 2.62/0.97  --extra_neg_conj                        none
% 2.62/0.97  --large_theory_mode                     true
% 2.62/0.97  --prolific_symb_bound                   200
% 2.62/0.97  --lt_threshold                          2000
% 2.62/0.97  --clause_weak_htbl                      true
% 2.62/0.97  --gc_record_bc_elim                     false
% 2.62/0.97  
% 2.62/0.97  ------ Preprocessing Options
% 2.62/0.97  
% 2.62/0.97  --preprocessing_flag                    true
% 2.62/0.97  --time_out_prep_mult                    0.1
% 2.62/0.97  --splitting_mode                        input
% 2.62/0.97  --splitting_grd                         true
% 2.62/0.97  --splitting_cvd                         false
% 2.62/0.97  --splitting_cvd_svl                     false
% 2.62/0.97  --splitting_nvd                         32
% 2.62/0.97  --sub_typing                            true
% 2.62/0.97  --prep_gs_sim                           true
% 2.62/0.97  --prep_unflatten                        true
% 2.62/0.97  --prep_res_sim                          true
% 2.62/0.97  --prep_upred                            true
% 2.62/0.97  --prep_sem_filter                       exhaustive
% 2.62/0.97  --prep_sem_filter_out                   false
% 2.62/0.97  --pred_elim                             true
% 2.62/0.97  --res_sim_input                         true
% 2.62/0.97  --eq_ax_congr_red                       true
% 2.62/0.97  --pure_diseq_elim                       true
% 2.62/0.97  --brand_transform                       false
% 2.62/0.97  --non_eq_to_eq                          false
% 2.62/0.97  --prep_def_merge                        true
% 2.62/0.97  --prep_def_merge_prop_impl              false
% 2.62/0.97  --prep_def_merge_mbd                    true
% 2.62/0.97  --prep_def_merge_tr_red                 false
% 2.62/0.97  --prep_def_merge_tr_cl                  false
% 2.62/0.97  --smt_preprocessing                     true
% 2.62/0.97  --smt_ac_axioms                         fast
% 2.62/0.97  --preprocessed_out                      false
% 2.62/0.97  --preprocessed_stats                    false
% 2.62/0.97  
% 2.62/0.97  ------ Abstraction refinement Options
% 2.62/0.97  
% 2.62/0.97  --abstr_ref                             []
% 2.62/0.97  --abstr_ref_prep                        false
% 2.62/0.97  --abstr_ref_until_sat                   false
% 2.62/0.97  --abstr_ref_sig_restrict                funpre
% 2.62/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.97  --abstr_ref_under                       []
% 2.62/0.97  
% 2.62/0.97  ------ SAT Options
% 2.62/0.97  
% 2.62/0.97  --sat_mode                              false
% 2.62/0.97  --sat_fm_restart_options                ""
% 2.62/0.97  --sat_gr_def                            false
% 2.62/0.97  --sat_epr_types                         true
% 2.62/0.97  --sat_non_cyclic_types                  false
% 2.62/0.97  --sat_finite_models                     false
% 2.62/0.97  --sat_fm_lemmas                         false
% 2.62/0.97  --sat_fm_prep                           false
% 2.62/0.97  --sat_fm_uc_incr                        true
% 2.62/0.97  --sat_out_model                         small
% 2.62/0.97  --sat_out_clauses                       false
% 2.62/0.97  
% 2.62/0.97  ------ QBF Options
% 2.62/0.97  
% 2.62/0.97  --qbf_mode                              false
% 2.62/0.97  --qbf_elim_univ                         false
% 2.62/0.97  --qbf_dom_inst                          none
% 2.62/0.97  --qbf_dom_pre_inst                      false
% 2.62/0.97  --qbf_sk_in                             false
% 2.62/0.97  --qbf_pred_elim                         true
% 2.62/0.97  --qbf_split                             512
% 2.62/0.97  
% 2.62/0.97  ------ BMC1 Options
% 2.62/0.97  
% 2.62/0.97  --bmc1_incremental                      false
% 2.62/0.97  --bmc1_axioms                           reachable_all
% 2.62/0.97  --bmc1_min_bound                        0
% 2.62/0.97  --bmc1_max_bound                        -1
% 2.62/0.97  --bmc1_max_bound_default                -1
% 2.62/0.97  --bmc1_symbol_reachability              true
% 2.62/0.97  --bmc1_property_lemmas                  false
% 2.62/0.97  --bmc1_k_induction                      false
% 2.62/0.97  --bmc1_non_equiv_states                 false
% 2.62/0.97  --bmc1_deadlock                         false
% 2.62/0.97  --bmc1_ucm                              false
% 2.62/0.97  --bmc1_add_unsat_core                   none
% 2.62/0.97  --bmc1_unsat_core_children              false
% 2.62/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.97  --bmc1_out_stat                         full
% 2.62/0.97  --bmc1_ground_init                      false
% 2.62/0.97  --bmc1_pre_inst_next_state              false
% 2.62/0.97  --bmc1_pre_inst_state                   false
% 2.62/0.97  --bmc1_pre_inst_reach_state             false
% 2.62/0.97  --bmc1_out_unsat_core                   false
% 2.62/0.97  --bmc1_aig_witness_out                  false
% 2.62/0.97  --bmc1_verbose                          false
% 2.62/0.97  --bmc1_dump_clauses_tptp                false
% 2.62/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.97  --bmc1_dump_file                        -
% 2.62/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.97  --bmc1_ucm_extend_mode                  1
% 2.62/0.97  --bmc1_ucm_init_mode                    2
% 2.62/0.97  --bmc1_ucm_cone_mode                    none
% 2.62/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.97  --bmc1_ucm_relax_model                  4
% 2.62/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.97  --bmc1_ucm_layered_model                none
% 2.62/0.97  --bmc1_ucm_max_lemma_size               10
% 2.62/0.97  
% 2.62/0.97  ------ AIG Options
% 2.62/0.97  
% 2.62/0.97  --aig_mode                              false
% 2.62/0.97  
% 2.62/0.97  ------ Instantiation Options
% 2.62/0.97  
% 2.62/0.97  --instantiation_flag                    true
% 2.62/0.97  --inst_sos_flag                         false
% 2.62/0.97  --inst_sos_phase                        true
% 2.62/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.97  --inst_lit_sel_side                     num_symb
% 2.62/0.97  --inst_solver_per_active                1400
% 2.62/0.97  --inst_solver_calls_frac                1.
% 2.62/0.97  --inst_passive_queue_type               priority_queues
% 2.62/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.97  --inst_passive_queues_freq              [25;2]
% 2.62/0.97  --inst_dismatching                      true
% 2.62/0.97  --inst_eager_unprocessed_to_passive     true
% 2.62/0.97  --inst_prop_sim_given                   true
% 2.62/0.97  --inst_prop_sim_new                     false
% 2.62/0.97  --inst_subs_new                         false
% 2.62/0.97  --inst_eq_res_simp                      false
% 2.62/0.97  --inst_subs_given                       false
% 2.62/0.97  --inst_orphan_elimination               true
% 2.62/0.97  --inst_learning_loop_flag               true
% 2.62/0.97  --inst_learning_start                   3000
% 2.62/0.97  --inst_learning_factor                  2
% 2.62/0.97  --inst_start_prop_sim_after_learn       3
% 2.62/0.97  --inst_sel_renew                        solver
% 2.62/0.97  --inst_lit_activity_flag                true
% 2.62/0.97  --inst_restr_to_given                   false
% 2.62/0.97  --inst_activity_threshold               500
% 2.62/0.97  --inst_out_proof                        true
% 2.62/0.97  
% 2.62/0.97  ------ Resolution Options
% 2.62/0.97  
% 2.62/0.97  --resolution_flag                       true
% 2.62/0.97  --res_lit_sel                           adaptive
% 2.62/0.97  --res_lit_sel_side                      none
% 2.62/0.97  --res_ordering                          kbo
% 2.62/0.97  --res_to_prop_solver                    active
% 2.62/0.97  --res_prop_simpl_new                    false
% 2.62/0.97  --res_prop_simpl_given                  true
% 2.62/0.97  --res_passive_queue_type                priority_queues
% 2.62/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.97  --res_passive_queues_freq               [15;5]
% 2.62/0.97  --res_forward_subs                      full
% 2.62/0.97  --res_backward_subs                     full
% 2.62/0.97  --res_forward_subs_resolution           true
% 2.62/0.97  --res_backward_subs_resolution          true
% 2.62/0.97  --res_orphan_elimination                true
% 2.62/0.97  --res_time_limit                        2.
% 2.62/0.97  --res_out_proof                         true
% 2.62/0.97  
% 2.62/0.97  ------ Superposition Options
% 2.62/0.97  
% 2.62/0.97  --superposition_flag                    true
% 2.62/0.97  --sup_passive_queue_type                priority_queues
% 2.62/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.97  --demod_completeness_check              fast
% 2.62/0.97  --demod_use_ground                      true
% 2.62/0.97  --sup_to_prop_solver                    passive
% 2.62/0.97  --sup_prop_simpl_new                    true
% 2.62/0.97  --sup_prop_simpl_given                  true
% 2.62/0.97  --sup_fun_splitting                     false
% 2.62/0.97  --sup_smt_interval                      50000
% 2.62/0.97  
% 2.62/0.97  ------ Superposition Simplification Setup
% 2.62/0.97  
% 2.62/0.97  --sup_indices_passive                   []
% 2.62/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.97  --sup_full_bw                           [BwDemod]
% 2.62/0.97  --sup_immed_triv                        [TrivRules]
% 2.62/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.97  --sup_immed_bw_main                     []
% 2.62/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.97  
% 2.62/0.97  ------ Combination Options
% 2.62/0.97  
% 2.62/0.97  --comb_res_mult                         3
% 2.62/0.97  --comb_sup_mult                         2
% 2.62/0.97  --comb_inst_mult                        10
% 2.62/0.97  
% 2.62/0.97  ------ Debug Options
% 2.62/0.97  
% 2.62/0.97  --dbg_backtrace                         false
% 2.62/0.97  --dbg_dump_prop_clauses                 false
% 2.62/0.97  --dbg_dump_prop_clauses_file            -
% 2.62/0.97  --dbg_out_stat                          false
% 2.62/0.97  ------ Parsing...
% 2.62/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/0.97  
% 2.62/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.62/0.97  
% 2.62/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/0.97  
% 2.62/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/0.97  ------ Proving...
% 2.62/0.97  ------ Problem Properties 
% 2.62/0.97  
% 2.62/0.97  
% 2.62/0.97  clauses                                 19
% 2.62/0.97  conjectures                             7
% 2.62/0.97  EPR                                     4
% 2.62/0.97  Horn                                    11
% 2.62/0.97  unary                                   6
% 2.62/0.97  binary                                  4
% 2.62/0.97  lits                                    73
% 2.62/0.97  lits eq                                 53
% 2.62/0.97  fd_pure                                 0
% 2.62/0.97  fd_pseudo                               0
% 2.62/0.97  fd_cond                                 5
% 2.62/0.97  fd_pseudo_cond                          5
% 2.62/0.97  AC symbols                              0
% 2.62/0.97  
% 2.62/0.97  ------ Schedule dynamic 5 is on 
% 2.62/0.97  
% 2.62/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/0.97  
% 2.62/0.97  
% 2.62/0.97  ------ 
% 2.62/0.97  Current options:
% 2.62/0.97  ------ 
% 2.62/0.97  
% 2.62/0.97  ------ Input Options
% 2.62/0.97  
% 2.62/0.97  --out_options                           all
% 2.62/0.97  --tptp_safe_out                         true
% 2.62/0.97  --problem_path                          ""
% 2.62/0.97  --include_path                          ""
% 2.62/0.97  --clausifier                            res/vclausify_rel
% 2.62/0.97  --clausifier_options                    --mode clausify
% 2.62/0.97  --stdin                                 false
% 2.62/0.97  --stats_out                             all
% 2.62/0.97  
% 2.62/0.97  ------ General Options
% 2.62/0.97  
% 2.62/0.97  --fof                                   false
% 2.62/0.97  --time_out_real                         305.
% 2.62/0.97  --time_out_virtual                      -1.
% 2.62/0.97  --symbol_type_check                     false
% 2.62/0.97  --clausify_out                          false
% 2.62/0.97  --sig_cnt_out                           false
% 2.62/0.97  --trig_cnt_out                          false
% 2.62/0.97  --trig_cnt_out_tolerance                1.
% 2.62/0.97  --trig_cnt_out_sk_spl                   false
% 2.62/0.97  --abstr_cl_out                          false
% 2.62/0.97  
% 2.62/0.97  ------ Global Options
% 2.62/0.97  
% 2.62/0.97  --schedule                              default
% 2.62/0.97  --add_important_lit                     false
% 2.62/0.97  --prop_solver_per_cl                    1000
% 2.62/0.97  --min_unsat_core                        false
% 2.62/0.97  --soft_assumptions                      false
% 2.62/0.97  --soft_lemma_size                       3
% 2.62/0.97  --prop_impl_unit_size                   0
% 2.62/0.97  --prop_impl_unit                        []
% 2.62/0.97  --share_sel_clauses                     true
% 2.62/0.97  --reset_solvers                         false
% 2.62/0.97  --bc_imp_inh                            [conj_cone]
% 2.62/0.97  --conj_cone_tolerance                   3.
% 2.62/0.97  --extra_neg_conj                        none
% 2.62/0.97  --large_theory_mode                     true
% 2.62/0.97  --prolific_symb_bound                   200
% 2.62/0.97  --lt_threshold                          2000
% 2.62/0.97  --clause_weak_htbl                      true
% 2.62/0.97  --gc_record_bc_elim                     false
% 2.62/0.97  
% 2.62/0.97  ------ Preprocessing Options
% 2.62/0.97  
% 2.62/0.97  --preprocessing_flag                    true
% 2.62/0.97  --time_out_prep_mult                    0.1
% 2.62/0.97  --splitting_mode                        input
% 2.62/0.97  --splitting_grd                         true
% 2.62/0.97  --splitting_cvd                         false
% 2.62/0.97  --splitting_cvd_svl                     false
% 2.62/0.97  --splitting_nvd                         32
% 2.62/0.97  --sub_typing                            true
% 2.62/0.97  --prep_gs_sim                           true
% 2.62/0.97  --prep_unflatten                        true
% 2.62/0.97  --prep_res_sim                          true
% 2.62/0.97  --prep_upred                            true
% 2.62/0.97  --prep_sem_filter                       exhaustive
% 2.62/0.97  --prep_sem_filter_out                   false
% 2.62/0.97  --pred_elim                             true
% 2.62/0.97  --res_sim_input                         true
% 2.62/0.97  --eq_ax_congr_red                       true
% 2.62/0.97  --pure_diseq_elim                       true
% 2.62/0.97  --brand_transform                       false
% 2.62/0.97  --non_eq_to_eq                          false
% 2.62/0.97  --prep_def_merge                        true
% 2.62/0.97  --prep_def_merge_prop_impl              false
% 2.62/0.97  --prep_def_merge_mbd                    true
% 2.62/0.97  --prep_def_merge_tr_red                 false
% 2.62/0.97  --prep_def_merge_tr_cl                  false
% 2.62/0.97  --smt_preprocessing                     true
% 2.62/0.97  --smt_ac_axioms                         fast
% 2.62/0.97  --preprocessed_out                      false
% 2.62/0.97  --preprocessed_stats                    false
% 2.62/0.97  
% 2.62/0.97  ------ Abstraction refinement Options
% 2.62/0.97  
% 2.62/0.97  --abstr_ref                             []
% 2.62/0.97  --abstr_ref_prep                        false
% 2.62/0.97  --abstr_ref_until_sat                   false
% 2.62/0.97  --abstr_ref_sig_restrict                funpre
% 2.62/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.97  --abstr_ref_under                       []
% 2.62/0.97  
% 2.62/0.97  ------ SAT Options
% 2.62/0.97  
% 2.62/0.97  --sat_mode                              false
% 2.62/0.97  --sat_fm_restart_options                ""
% 2.62/0.97  --sat_gr_def                            false
% 2.62/0.97  --sat_epr_types                         true
% 2.62/0.97  --sat_non_cyclic_types                  false
% 2.62/0.97  --sat_finite_models                     false
% 2.62/0.97  --sat_fm_lemmas                         false
% 2.62/0.97  --sat_fm_prep                           false
% 2.62/0.97  --sat_fm_uc_incr                        true
% 2.62/0.97  --sat_out_model                         small
% 2.62/0.97  --sat_out_clauses                       false
% 2.62/0.97  
% 2.62/0.97  ------ QBF Options
% 2.62/0.97  
% 2.62/0.97  --qbf_mode                              false
% 2.62/0.97  --qbf_elim_univ                         false
% 2.62/0.97  --qbf_dom_inst                          none
% 2.62/0.97  --qbf_dom_pre_inst                      false
% 2.62/0.97  --qbf_sk_in                             false
% 2.62/0.97  --qbf_pred_elim                         true
% 2.62/0.97  --qbf_split                             512
% 2.62/0.97  
% 2.62/0.97  ------ BMC1 Options
% 2.62/0.97  
% 2.62/0.97  --bmc1_incremental                      false
% 2.62/0.97  --bmc1_axioms                           reachable_all
% 2.62/0.97  --bmc1_min_bound                        0
% 2.62/0.97  --bmc1_max_bound                        -1
% 2.62/0.97  --bmc1_max_bound_default                -1
% 2.62/0.97  --bmc1_symbol_reachability              true
% 2.62/0.97  --bmc1_property_lemmas                  false
% 2.62/0.97  --bmc1_k_induction                      false
% 2.62/0.97  --bmc1_non_equiv_states                 false
% 2.62/0.97  --bmc1_deadlock                         false
% 2.62/0.97  --bmc1_ucm                              false
% 2.62/0.97  --bmc1_add_unsat_core                   none
% 2.62/0.97  --bmc1_unsat_core_children              false
% 2.62/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.97  --bmc1_out_stat                         full
% 2.62/0.97  --bmc1_ground_init                      false
% 2.62/0.97  --bmc1_pre_inst_next_state              false
% 2.62/0.97  --bmc1_pre_inst_state                   false
% 2.62/0.97  --bmc1_pre_inst_reach_state             false
% 2.62/0.97  --bmc1_out_unsat_core                   false
% 2.62/0.97  --bmc1_aig_witness_out                  false
% 2.62/0.97  --bmc1_verbose                          false
% 2.62/0.97  --bmc1_dump_clauses_tptp                false
% 2.62/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.97  --bmc1_dump_file                        -
% 2.62/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.97  --bmc1_ucm_extend_mode                  1
% 2.62/0.97  --bmc1_ucm_init_mode                    2
% 2.62/0.97  --bmc1_ucm_cone_mode                    none
% 2.62/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.97  --bmc1_ucm_relax_model                  4
% 2.62/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.97  --bmc1_ucm_layered_model                none
% 2.62/0.97  --bmc1_ucm_max_lemma_size               10
% 2.62/0.97  
% 2.62/0.97  ------ AIG Options
% 2.62/0.97  
% 2.62/0.97  --aig_mode                              false
% 2.62/0.97  
% 2.62/0.97  ------ Instantiation Options
% 2.62/0.97  
% 2.62/0.97  --instantiation_flag                    true
% 2.62/0.97  --inst_sos_flag                         false
% 2.62/0.97  --inst_sos_phase                        true
% 2.62/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.97  --inst_lit_sel_side                     none
% 2.62/0.97  --inst_solver_per_active                1400
% 2.62/0.97  --inst_solver_calls_frac                1.
% 2.62/0.97  --inst_passive_queue_type               priority_queues
% 2.62/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.97  --inst_passive_queues_freq              [25;2]
% 2.62/0.98  --inst_dismatching                      true
% 2.62/0.98  --inst_eager_unprocessed_to_passive     true
% 2.62/0.98  --inst_prop_sim_given                   true
% 2.62/0.98  --inst_prop_sim_new                     false
% 2.62/0.98  --inst_subs_new                         false
% 2.62/0.98  --inst_eq_res_simp                      false
% 2.62/0.98  --inst_subs_given                       false
% 2.62/0.98  --inst_orphan_elimination               true
% 2.62/0.98  --inst_learning_loop_flag               true
% 2.62/0.98  --inst_learning_start                   3000
% 2.62/0.98  --inst_learning_factor                  2
% 2.62/0.98  --inst_start_prop_sim_after_learn       3
% 2.62/0.98  --inst_sel_renew                        solver
% 2.62/0.98  --inst_lit_activity_flag                true
% 2.62/0.98  --inst_restr_to_given                   false
% 2.62/0.98  --inst_activity_threshold               500
% 2.62/0.98  --inst_out_proof                        true
% 2.62/0.98  
% 2.62/0.98  ------ Resolution Options
% 2.62/0.98  
% 2.62/0.98  --resolution_flag                       false
% 2.62/0.98  --res_lit_sel                           adaptive
% 2.62/0.98  --res_lit_sel_side                      none
% 2.62/0.98  --res_ordering                          kbo
% 2.62/0.98  --res_to_prop_solver                    active
% 2.62/0.98  --res_prop_simpl_new                    false
% 2.62/0.98  --res_prop_simpl_given                  true
% 2.62/0.98  --res_passive_queue_type                priority_queues
% 2.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.98  --res_passive_queues_freq               [15;5]
% 2.62/0.98  --res_forward_subs                      full
% 2.62/0.98  --res_backward_subs                     full
% 2.62/0.98  --res_forward_subs_resolution           true
% 2.62/0.98  --res_backward_subs_resolution          true
% 2.62/0.98  --res_orphan_elimination                true
% 2.62/0.98  --res_time_limit                        2.
% 2.62/0.98  --res_out_proof                         true
% 2.62/0.98  
% 2.62/0.98  ------ Superposition Options
% 2.62/0.98  
% 2.62/0.98  --superposition_flag                    true
% 2.62/0.98  --sup_passive_queue_type                priority_queues
% 2.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.98  --demod_completeness_check              fast
% 2.62/0.98  --demod_use_ground                      true
% 2.62/0.98  --sup_to_prop_solver                    passive
% 2.62/0.98  --sup_prop_simpl_new                    true
% 2.62/0.98  --sup_prop_simpl_given                  true
% 2.62/0.98  --sup_fun_splitting                     false
% 2.62/0.98  --sup_smt_interval                      50000
% 2.62/0.98  
% 2.62/0.98  ------ Superposition Simplification Setup
% 2.62/0.98  
% 2.62/0.98  --sup_indices_passive                   []
% 2.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_full_bw                           [BwDemod]
% 2.62/0.98  --sup_immed_triv                        [TrivRules]
% 2.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_immed_bw_main                     []
% 2.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.98  
% 2.62/0.98  ------ Combination Options
% 2.62/0.98  
% 2.62/0.98  --comb_res_mult                         3
% 2.62/0.98  --comb_sup_mult                         2
% 2.62/0.98  --comb_inst_mult                        10
% 2.62/0.98  
% 2.62/0.98  ------ Debug Options
% 2.62/0.98  
% 2.62/0.98  --dbg_backtrace                         false
% 2.62/0.98  --dbg_dump_prop_clauses                 false
% 2.62/0.98  --dbg_dump_prop_clauses_file            -
% 2.62/0.98  --dbg_out_stat                          false
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  ------ Proving...
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  % SZS status Theorem for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  fof(f4,conjecture,(
% 2.62/0.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f5,negated_conjecture,(
% 2.62/0.98    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.62/0.98    inference(negated_conjecture,[],[f4])).
% 2.62/0.98  
% 2.62/0.98  fof(f9,plain,(
% 2.62/0.98    ? [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.62/0.98    inference(ennf_transformation,[],[f5])).
% 2.62/0.98  
% 2.62/0.98  fof(f10,plain,(
% 2.62/0.98    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.62/0.98    inference(flattening,[],[f9])).
% 2.62/0.98  
% 2.62/0.98  fof(f20,plain,(
% 2.62/0.98    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12 & k1_xboole_0 != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK12 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK13 | ~m1_subset_1(X9,sK11)) | ~m1_subset_1(X8,sK10)) | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) & m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f21,plain,(
% 2.62/0.98    k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12 & k1_xboole_0 != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK12 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK13 | ~m1_subset_1(X9,sK11)) | ~m1_subset_1(X8,sK10)) | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) & m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11))),
% 2.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12,sK13])],[f10,f20])).
% 2.62/0.98  
% 2.62/0.98  fof(f34,plain,(
% 2.62/0.98    m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11))),
% 2.62/0.98    inference(cnf_transformation,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f2,axiom,(
% 2.62/0.98    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f7,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.62/0.98    inference(ennf_transformation,[],[f2])).
% 2.62/0.98  
% 2.62/0.98  fof(f18,plain,(
% 2.62/0.98    ( ! [X6,X7,X5] : (! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(X5,X6,X7,sK7(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK7(X0,X1,X2,X3,X4),X3)))) )),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f17,plain,(
% 2.62/0.98    ( ! [X6,X5] : (! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(X5,X6,sK6(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X2)))) )),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f16,plain,(
% 2.62/0.98    ( ! [X5] : (! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(X5,sK5(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X1)))) )),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f15,plain,(
% 2.62/0.98    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK4(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK4(X0,X1,X2,X3,X4),X0)))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f19,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK7(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK4(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f7,f18,f17,f16,f15])).
% 2.62/0.98  
% 2.62/0.98  fof(f25,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f1,axiom,(
% 2.62/0.98    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X0) => (k8_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X6)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f6,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k8_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X6 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.62/0.98    inference(ennf_transformation,[],[f1])).
% 2.62/0.98  
% 2.62/0.98  fof(f11,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X6 | k4_mcart_1(X6,X7,X8,X9) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.62/0.98    inference(nnf_transformation,[],[f6])).
% 2.62/0.98  
% 2.62/0.98  fof(f12,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.62/0.98    inference(rectify,[],[f11])).
% 2.62/0.98  
% 2.62/0.98  fof(f13,plain,(
% 2.62/0.98    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK0(X4,X5) != X5 & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f14,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK0(X4,X5) != X5 & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).
% 2.62/0.98  
% 2.62/0.98  fof(f23,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.62/0.98    inference(cnf_transformation,[],[f14])).
% 2.62/0.98  
% 2.62/0.98  fof(f36,plain,(
% 2.62/0.98    k1_xboole_0 != sK8),
% 2.62/0.98    inference(cnf_transformation,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f37,plain,(
% 2.62/0.98    k1_xboole_0 != sK9),
% 2.62/0.98    inference(cnf_transformation,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f38,plain,(
% 2.62/0.98    k1_xboole_0 != sK10),
% 2.62/0.98    inference(cnf_transformation,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f39,plain,(
% 2.62/0.98    k1_xboole_0 != sK11),
% 2.62/0.98    inference(cnf_transformation,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f26,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f27,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f28,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f29,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f35,plain,(
% 2.62/0.98    ( ! [X6,X8,X7,X9] : (sK12 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK13 | ~m1_subset_1(X9,sK11) | ~m1_subset_1(X8,sK10) | ~m1_subset_1(X7,sK9) | ~m1_subset_1(X6,sK8)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f40,plain,(
% 2.62/0.98    k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12),
% 2.62/0.98    inference(cnf_transformation,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f3,axiom,(
% 2.62/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f8,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7))),
% 2.62/0.98    inference(ennf_transformation,[],[f3])).
% 2.62/0.98  
% 2.62/0.98  fof(f30,plain,(
% 2.62/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 = X4 | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f8])).
% 2.62/0.98  
% 2.62/0.98  fof(f24,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | sK0(X4,X5) != X5 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.62/0.98    inference(cnf_transformation,[],[f14])).
% 2.62/0.98  
% 2.62/0.98  cnf(c_18,negated_conjecture,
% 2.62/0.98      ( m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) ),
% 2.62/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_291,plain,
% 2.62/0.98      ( m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_7,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.62/0.98      | m1_subset_1(sK4(X1,X2,X3,X4,X0),X1)
% 2.62/0.98      | k1_xboole_0 = X4
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1 ),
% 2.62/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_293,plain,
% 2.62/0.98      ( k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
% 2.62/0.98      | m1_subset_1(sK4(X2,X1,X0,X3,X4),X2) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,X1)
% 2.62/0.98      | ~ m1_subset_1(X2,k4_zfmisc_1(X1,X3,X4,X5))
% 2.62/0.98      | k8_mcart_1(X1,X3,X4,X5,X2) = X0
% 2.62/0.98      | k4_mcart_1(sK0(X2,X0),sK1(X2,X0),sK2(X2,X0),sK3(X2,X0)) = X2
% 2.62/0.98      | k1_xboole_0 = X5
% 2.62/0.98      | k1_xboole_0 = X4
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X1 ),
% 2.62/0.98      inference(cnf_transformation,[],[f23]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_299,plain,
% 2.62/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.62/0.98      | k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | m1_subset_1(X5,X0) != iProver_top
% 2.62/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3081,plain,
% 2.62/0.98      ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = X0
% 2.62/0.98      | k4_mcart_1(sK0(sK13,X0),sK1(sK13,X0),sK2(sK13,X0),sK3(sK13,X0)) = sK13
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | m1_subset_1(X0,sK8) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_291,c_299]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_16,negated_conjecture,
% 2.62/0.98      ( k1_xboole_0 != sK8 ),
% 2.62/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_15,negated_conjecture,
% 2.62/0.98      ( k1_xboole_0 != sK9 ),
% 2.62/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_14,negated_conjecture,
% 2.62/0.98      ( k1_xboole_0 != sK10 ),
% 2.62/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_13,negated_conjecture,
% 2.62/0.98      ( k1_xboole_0 != sK11 ),
% 2.62/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_126,plain,( X0 = X0 ),theory(equality) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_137,plain,
% 2.62/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_126]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_127,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_470,plain,
% 2.62/0.98      ( sK11 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK11 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_127]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_471,plain,
% 2.62/0.98      ( sK11 != k1_xboole_0
% 2.62/0.98      | k1_xboole_0 = sK11
% 2.62/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_470]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_472,plain,
% 2.62/0.98      ( sK10 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK10 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_127]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_473,plain,
% 2.62/0.98      ( sK10 != k1_xboole_0
% 2.62/0.98      | k1_xboole_0 = sK10
% 2.62/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_472]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_474,plain,
% 2.62/0.98      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_127]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_475,plain,
% 2.62/0.98      ( sK9 != k1_xboole_0
% 2.62/0.98      | k1_xboole_0 = sK9
% 2.62/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_474]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_476,plain,
% 2.62/0.98      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_127]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_477,plain,
% 2.62/0.98      ( sK8 != k1_xboole_0
% 2.62/0.98      | k1_xboole_0 = sK8
% 2.62/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_476]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3204,plain,
% 2.62/0.98      ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = X0
% 2.62/0.98      | k4_mcart_1(sK0(sK13,X0),sK1(sK13,X0),sK2(sK13,X0),sK3(sK13,X0)) = sK13
% 2.62/0.98      | m1_subset_1(X0,sK8) != iProver_top ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_3081,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,
% 2.62/0.98                 c_477]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3213,plain,
% 2.62/0.98      ( sK4(sK8,X0,X1,X2,X3) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
% 2.62/0.98      | k4_mcart_1(sK0(sK13,sK4(sK8,X0,X1,X2,X3)),sK1(sK13,sK4(sK8,X0,X1,X2,X3)),sK2(sK13,sK4(sK8,X0,X1,X2,X3)),sK3(sK13,sK4(sK8,X0,X1,X2,X3))) = sK13
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | m1_subset_1(X3,k4_zfmisc_1(sK8,X0,X1,X2)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_293,c_3204]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3857,plain,
% 2.62/0.98      ( k4_mcart_1(sK0(sK13,sK4(sK8,X0,X1,X2,X3)),sK1(sK13,sK4(sK8,X0,X1,X2,X3)),sK2(sK13,sK4(sK8,X0,X1,X2,X3)),sK3(sK13,sK4(sK8,X0,X1,X2,X3))) = sK13
% 2.62/0.98      | sK4(sK8,X0,X1,X2,X3) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | m1_subset_1(X3,k4_zfmisc_1(sK8,X0,X1,X2)) != iProver_top ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_3213,c_16,c_137,c_477]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3858,plain,
% 2.62/0.98      ( sK4(sK8,X0,X1,X2,X3) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
% 2.62/0.98      | k4_mcart_1(sK0(sK13,sK4(sK8,X0,X1,X2,X3)),sK1(sK13,sK4(sK8,X0,X1,X2,X3)),sK2(sK13,sK4(sK8,X0,X1,X2,X3)),sK3(sK13,sK4(sK8,X0,X1,X2,X3))) = sK13
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X0
% 2.62/0.98      | m1_subset_1(X3,k4_zfmisc_1(sK8,X0,X1,X2)) != iProver_top ),
% 2.62/0.98      inference(renaming,[status(thm)],[c_3857]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3867,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
% 2.62/0.98      | k4_mcart_1(sK0(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK1(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK2(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK3(sK13,sK4(sK8,sK9,sK10,sK11,sK13))) = sK13
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0 ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_291,c_3858]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4999,plain,
% 2.62/0.98      ( k4_mcart_1(sK0(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK1(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK2(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK3(sK13,sK4(sK8,sK9,sK10,sK11,sK13))) = sK13
% 2.62/0.98      | sK4(sK8,sK9,sK10,sK11,sK13) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13) ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_3867,c_15,c_14,c_13,c_137,c_471,c_473,c_475]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_5000,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = k8_mcart_1(sK8,sK9,sK10,sK11,sK13)
% 2.62/0.98      | k4_mcart_1(sK0(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK1(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK2(sK13,sK4(sK8,sK9,sK10,sK11,sK13)),sK3(sK13,sK4(sK8,sK9,sK10,sK11,sK13))) = sK13 ),
% 2.62/0.98      inference(renaming,[status(thm)],[c_4999]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_6,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.62/0.98      | m1_subset_1(sK5(X1,X2,X3,X4,X0),X2)
% 2.62/0.98      | k1_xboole_0 = X4
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1 ),
% 2.62/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_294,plain,
% 2.62/0.98      ( k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
% 2.62/0.98      | m1_subset_1(sK5(X2,X1,X0,X3,X4),X1) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_5,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.62/0.98      | m1_subset_1(sK6(X1,X2,X3,X4,X0),X3)
% 2.62/0.98      | k1_xboole_0 = X4
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1 ),
% 2.62/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_295,plain,
% 2.62/0.98      ( k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
% 2.62/0.98      | m1_subset_1(sK6(X2,X1,X0,X3,X4),X0) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.62/0.98      | m1_subset_1(sK7(X1,X2,X3,X4,X0),X4)
% 2.62/0.98      | k1_xboole_0 = X4
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1 ),
% 2.62/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_296,plain,
% 2.62/0.98      ( k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | m1_subset_1(X4,k4_zfmisc_1(X2,X1,X0,X3)) != iProver_top
% 2.62/0.98      | m1_subset_1(sK7(X2,X1,X0,X3,X4),X3) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.62/0.98      | k4_mcart_1(sK4(X1,X2,X3,X4,X0),sK5(X1,X2,X3,X4,X0),sK6(X1,X2,X3,X4,X0),sK7(X1,X2,X3,X4,X0)) = X0
% 2.62/0.98      | k1_xboole_0 = X4
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1 ),
% 2.62/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_297,plain,
% 2.62/0.98      ( k4_mcart_1(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1589,plain,
% 2.62/0.98      ( k4_mcart_1(sK4(sK8,sK9,sK10,sK11,sK13),sK5(sK8,sK9,sK10,sK11,sK13),sK6(sK8,sK9,sK10,sK11,sK13),sK7(sK8,sK9,sK10,sK11,sK13)) = sK13
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0 ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_291,c_297]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1688,plain,
% 2.62/0.98      ( k4_mcart_1(sK4(sK8,sK9,sK10,sK11,sK13),sK5(sK8,sK9,sK10,sK11,sK13),sK6(sK8,sK9,sK10,sK11,sK13),sK7(sK8,sK9,sK10,sK11,sK13)) = sK13 ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_1589,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,
% 2.62/0.98                 c_477]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_17,negated_conjecture,
% 2.62/0.98      ( ~ m1_subset_1(X0,sK11)
% 2.62/0.98      | ~ m1_subset_1(X1,sK10)
% 2.62/0.98      | ~ m1_subset_1(X2,sK9)
% 2.62/0.98      | ~ m1_subset_1(X3,sK8)
% 2.62/0.98      | k4_mcart_1(X3,X2,X1,X0) != sK13
% 2.62/0.98      | sK12 = X3 ),
% 2.62/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_292,plain,
% 2.62/0.98      ( k4_mcart_1(X0,X1,X2,X3) != sK13
% 2.62/0.98      | sK12 = X0
% 2.62/0.98      | m1_subset_1(X3,sK11) != iProver_top
% 2.62/0.98      | m1_subset_1(X2,sK10) != iProver_top
% 2.62/0.98      | m1_subset_1(X1,sK9) != iProver_top
% 2.62/0.98      | m1_subset_1(X0,sK8) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1691,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | m1_subset_1(sK7(sK8,sK9,sK10,sK11,sK13),sK11) != iProver_top
% 2.62/0.98      | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
% 2.62/0.98      | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
% 2.62/0.98      | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_1688,c_292]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2004,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
% 2.62/0.98      | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
% 2.62/0.98      | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
% 2.62/0.98      | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_296,c_1691]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_19,plain,
% 2.62/0.98      ( m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3556,plain,
% 2.62/0.98      ( m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
% 2.62/0.98      | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
% 2.62/0.98      | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
% 2.62/0.98      | sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_2004,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,
% 2.62/0.98                 c_477]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3557,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | m1_subset_1(sK6(sK8,sK9,sK10,sK11,sK13),sK10) != iProver_top
% 2.62/0.98      | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
% 2.62/0.98      | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
% 2.62/0.98      inference(renaming,[status(thm)],[c_3556]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3564,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
% 2.62/0.98      | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
% 2.62/0.98      | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_295,c_3557]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4388,plain,
% 2.62/0.98      ( m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
% 2.62/0.98      | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
% 2.62/0.98      | sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_3564,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,
% 2.62/0.98                 c_477]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4389,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | m1_subset_1(sK5(sK8,sK9,sK10,sK11,sK13),sK9) != iProver_top
% 2.62/0.98      | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
% 2.62/0.98      inference(renaming,[status(thm)],[c_4388]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4395,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
% 2.62/0.98      | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_294,c_4389]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4398,plain,
% 2.62/0.98      ( m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top
% 2.62/0.98      | sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_4395,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,
% 2.62/0.98                 c_477]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4399,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | m1_subset_1(sK4(sK8,sK9,sK10,sK11,sK13),sK8) != iProver_top ),
% 2.62/0.98      inference(renaming,[status(thm)],[c_4398]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4404,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_293,c_4399]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4677,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = sK12 ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_4404,c_19,c_16,c_15,c_14,c_13,c_137,c_471,c_473,c_475,
% 2.62/0.98                 c_477]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_5001,plain,
% 2.62/0.98      ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | k4_mcart_1(sK0(sK13,sK12),sK1(sK13,sK12),sK2(sK13,sK12),sK3(sK13,sK12)) = sK13 ),
% 2.62/0.98      inference(light_normalisation,[status(thm)],[c_5000,c_4677]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_12,negated_conjecture,
% 2.62/0.98      ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) != sK12 ),
% 2.62/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_5004,plain,
% 2.62/0.98      ( k4_mcart_1(sK0(sK13,sK12),sK1(sK13,sK12),sK2(sK13,sK12),sK3(sK13,sK12)) = sK13 ),
% 2.62/0.98      inference(forward_subsumption_resolution,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_5001,c_12]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_11,plain,
% 2.62/0.98      ( X0 = X1 | k4_mcart_1(X0,X2,X3,X4) != k4_mcart_1(X1,X5,X6,X7) ),
% 2.62/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1698,plain,
% 2.62/0.98      ( sK4(sK8,sK9,sK10,sK11,sK13) = X0
% 2.62/0.98      | k4_mcart_1(X0,X1,X2,X3) != sK13 ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_1688,c_11]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4681,plain,
% 2.62/0.98      ( k4_mcart_1(X0,X1,X2,X3) != sK13 | sK12 = X0 ),
% 2.62/0.98      inference(demodulation,[status(thm)],[c_4677,c_1698]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_5006,plain,
% 2.62/0.98      ( sK0(sK13,sK12) = sK12 ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_5004,c_4681]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_0,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,X1)
% 2.62/0.98      | ~ m1_subset_1(X2,k4_zfmisc_1(X1,X3,X4,X5))
% 2.62/0.98      | k8_mcart_1(X1,X3,X4,X5,X2) = X0
% 2.62/0.98      | sK0(X2,X0) != X0
% 2.62/0.98      | k1_xboole_0 = X5
% 2.62/0.98      | k1_xboole_0 = X4
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X1 ),
% 2.62/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_300,plain,
% 2.62/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.62/0.98      | sK0(X4,X5) != X5
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X0
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | m1_subset_1(X5,X0) != iProver_top
% 2.62/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_5049,plain,
% 2.62/0.98      ( k8_mcart_1(X0,X1,X2,X3,sK13) = sK12
% 2.62/0.98      | k1_xboole_0 = X3
% 2.62/0.98      | k1_xboole_0 = X2
% 2.62/0.98      | k1_xboole_0 = X1
% 2.62/0.98      | k1_xboole_0 = X0
% 2.62/0.98      | m1_subset_1(sK12,X0) != iProver_top
% 2.62/0.98      | m1_subset_1(sK13,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_5006,c_300]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_6221,plain,
% 2.62/0.98      ( k8_mcart_1(sK8,sK9,sK10,sK11,sK13) = sK12
% 2.62/0.98      | sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | m1_subset_1(sK12,sK8) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_291,c_5049]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4705,plain,
% 2.62/0.98      ( sK11 = k1_xboole_0
% 2.62/0.98      | sK10 = k1_xboole_0
% 2.62/0.98      | sK9 = k1_xboole_0
% 2.62/0.98      | sK8 = k1_xboole_0
% 2.62/0.98      | m1_subset_1(sK12,sK8) = iProver_top
% 2.62/0.98      | m1_subset_1(sK13,k4_zfmisc_1(sK8,sK9,sK10,sK11)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_4677,c_293]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(contradiction,plain,
% 2.62/0.98      ( $false ),
% 2.62/0.98      inference(minisat,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_6221,c_4705,c_477,c_475,c_473,c_471,c_137,c_12,c_13,
% 2.62/0.98                 c_14,c_15,c_16,c_19]) ).
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  ------                               Statistics
% 2.62/0.98  
% 2.62/0.98  ------ General
% 2.62/0.98  
% 2.62/0.98  abstr_ref_over_cycles:                  0
% 2.62/0.98  abstr_ref_under_cycles:                 0
% 2.62/0.98  gc_basic_clause_elim:                   0
% 2.62/0.98  forced_gc_time:                         0
% 2.62/0.98  parsing_time:                           0.01
% 2.62/0.98  unif_index_cands_time:                  0.
% 2.62/0.98  unif_index_add_time:                    0.
% 2.62/0.98  orderings_time:                         0.
% 2.62/0.98  out_proof_time:                         0.011
% 2.62/0.98  total_time:                             0.257
% 2.62/0.98  num_of_symbols:                         50
% 2.62/0.98  num_of_terms:                           16830
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing
% 2.62/0.98  
% 2.62/0.98  num_of_splits:                          0
% 2.62/0.98  num_of_split_atoms:                     0
% 2.62/0.98  num_of_reused_defs:                     0
% 2.62/0.98  num_eq_ax_congr_red:                    56
% 2.62/0.98  num_of_sem_filtered_clauses:            1
% 2.62/0.98  num_of_subtypes:                        0
% 2.62/0.98  monotx_restored_types:                  0
% 2.62/0.98  sat_num_of_epr_types:                   0
% 2.62/0.98  sat_num_of_non_cyclic_types:            0
% 2.62/0.98  sat_guarded_non_collapsed_types:        0
% 2.62/0.98  num_pure_diseq_elim:                    0
% 2.62/0.98  simp_replaced_by:                       0
% 2.62/0.98  res_preprocessed:                       70
% 2.62/0.98  prep_upred:                             0
% 2.62/0.98  prep_unflattend:                        0
% 2.62/0.98  smt_new_axioms:                         0
% 2.62/0.98  pred_elim_cands:                        1
% 2.62/0.98  pred_elim:                              0
% 2.62/0.98  pred_elim_cl:                           0
% 2.62/0.98  pred_elim_cycles:                       1
% 2.62/0.98  merged_defs:                            0
% 2.62/0.98  merged_defs_ncl:                        0
% 2.62/0.98  bin_hyper_res:                          0
% 2.62/0.98  prep_cycles:                            3
% 2.62/0.98  pred_elim_time:                         0.
% 2.62/0.98  splitting_time:                         0.
% 2.62/0.98  sem_filter_time:                        0.
% 2.62/0.98  monotx_time:                            0.
% 2.62/0.98  subtype_inf_time:                       0.
% 2.62/0.98  
% 2.62/0.98  ------ Problem properties
% 2.62/0.98  
% 2.62/0.98  clauses:                                19
% 2.62/0.98  conjectures:                            7
% 2.62/0.98  epr:                                    4
% 2.62/0.98  horn:                                   11
% 2.62/0.98  ground:                                 6
% 2.62/0.98  unary:                                  6
% 2.62/0.98  binary:                                 4
% 2.62/0.98  lits:                                   73
% 2.62/0.98  lits_eq:                                53
% 2.62/0.98  fd_pure:                                0
% 2.62/0.98  fd_pseudo:                              0
% 2.62/0.98  fd_cond:                                5
% 2.62/0.98  fd_pseudo_cond:                         5
% 2.62/0.98  ac_symbols:                             0
% 2.62/0.98  
% 2.62/0.98  ------ Propositional Solver
% 2.62/0.98  
% 2.62/0.98  prop_solver_calls:                      23
% 2.62/0.98  prop_fast_solver_calls:                 768
% 2.62/0.98  smt_solver_calls:                       0
% 2.62/0.98  smt_fast_solver_calls:                  0
% 2.62/0.98  prop_num_of_clauses:                    2881
% 2.62/0.98  prop_preprocess_simplified:             8800
% 2.62/0.98  prop_fo_subsumed:                       47
% 2.62/0.98  prop_solver_time:                       0.
% 2.62/0.98  smt_solver_time:                        0.
% 2.62/0.98  smt_fast_solver_time:                   0.
% 2.62/0.98  prop_fast_solver_time:                  0.
% 2.62/0.98  prop_unsat_core_time:                   0.
% 2.62/0.98  
% 2.62/0.98  ------ QBF
% 2.62/0.98  
% 2.62/0.98  qbf_q_res:                              0
% 2.62/0.98  qbf_num_tautologies:                    0
% 2.62/0.98  qbf_prep_cycles:                        0
% 2.62/0.98  
% 2.62/0.98  ------ BMC1
% 2.62/0.98  
% 2.62/0.98  bmc1_current_bound:                     -1
% 2.62/0.98  bmc1_last_solved_bound:                 -1
% 2.62/0.98  bmc1_unsat_core_size:                   -1
% 2.62/0.98  bmc1_unsat_core_parents_size:           -1
% 2.62/0.98  bmc1_merge_next_fun:                    0
% 2.62/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.62/0.98  
% 2.62/0.98  ------ Instantiation
% 2.62/0.98  
% 2.62/0.98  inst_num_of_clauses:                    946
% 2.62/0.98  inst_num_in_passive:                    695
% 2.62/0.98  inst_num_in_active:                     240
% 2.62/0.98  inst_num_in_unprocessed:                11
% 2.62/0.98  inst_num_of_loops:                      240
% 2.62/0.98  inst_num_of_learning_restarts:          0
% 2.62/0.98  inst_num_moves_active_passive:          0
% 2.62/0.98  inst_lit_activity:                      0
% 2.62/0.98  inst_lit_activity_moves:                0
% 2.62/0.98  inst_num_tautologies:                   0
% 2.62/0.98  inst_num_prop_implied:                  0
% 2.62/0.98  inst_num_existing_simplified:           0
% 2.62/0.98  inst_num_eq_res_simplified:             0
% 2.62/0.98  inst_num_child_elim:                    0
% 2.62/0.98  inst_num_of_dismatching_blockings:      5
% 2.62/0.98  inst_num_of_non_proper_insts:           774
% 2.62/0.98  inst_num_of_duplicates:                 0
% 2.62/0.98  inst_inst_num_from_inst_to_res:         0
% 2.62/0.98  inst_dismatching_checking_time:         0.
% 2.62/0.98  
% 2.62/0.98  ------ Resolution
% 2.62/0.98  
% 2.62/0.98  res_num_of_clauses:                     0
% 2.62/0.98  res_num_in_passive:                     0
% 2.62/0.98  res_num_in_active:                      0
% 2.62/0.98  res_num_of_loops:                       73
% 2.62/0.98  res_forward_subset_subsumed:            27
% 2.62/0.98  res_backward_subset_subsumed:           0
% 2.62/0.98  res_forward_subsumed:                   0
% 2.62/0.98  res_backward_subsumed:                  0
% 2.62/0.98  res_forward_subsumption_resolution:     0
% 2.62/0.98  res_backward_subsumption_resolution:    0
% 2.62/0.98  res_clause_to_clause_subsumption:       311
% 2.62/0.98  res_orphan_elimination:                 0
% 2.62/0.98  res_tautology_del:                      2
% 2.62/0.98  res_num_eq_res_simplified:              0
% 2.62/0.98  res_num_sel_changes:                    0
% 2.62/0.98  res_moves_from_active_to_pass:          0
% 2.62/0.98  
% 2.62/0.98  ------ Superposition
% 2.62/0.98  
% 2.62/0.98  sup_time_total:                         0.
% 2.62/0.98  sup_time_generating:                    0.
% 2.62/0.98  sup_time_sim_full:                      0.
% 2.62/0.98  sup_time_sim_immed:                     0.
% 2.62/0.98  
% 2.62/0.98  sup_num_of_clauses:                     70
% 2.62/0.98  sup_num_in_active:                      36
% 2.62/0.98  sup_num_in_passive:                     34
% 2.62/0.98  sup_num_of_loops:                       47
% 2.62/0.98  sup_fw_superposition:                   40
% 2.62/0.98  sup_bw_superposition:                   37
% 2.62/0.98  sup_immediate_simplified:               4
% 2.62/0.98  sup_given_eliminated:                   1
% 2.62/0.98  comparisons_done:                       0
% 2.62/0.98  comparisons_avoided:                    63
% 2.62/0.98  
% 2.62/0.98  ------ Simplifications
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  sim_fw_subset_subsumed:                 0
% 2.62/0.98  sim_bw_subset_subsumed:                 5
% 2.62/0.98  sim_fw_subsumed:                        1
% 2.62/0.98  sim_bw_subsumed:                        0
% 2.62/0.98  sim_fw_subsumption_res:                 1
% 2.62/0.98  sim_bw_subsumption_res:                 0
% 2.62/0.98  sim_tautology_del:                      0
% 2.62/0.98  sim_eq_tautology_del:                   10
% 2.62/0.98  sim_eq_res_simp:                        0
% 2.62/0.98  sim_fw_demodulated:                     1
% 2.62/0.98  sim_bw_demodulated:                     8
% 2.62/0.98  sim_light_normalised:                   4
% 2.62/0.98  sim_joinable_taut:                      0
% 2.62/0.98  sim_joinable_simp:                      0
% 2.62/0.98  sim_ac_normalised:                      0
% 2.62/0.98  sim_smt_subsumption:                    0
% 2.62/0.98  
%------------------------------------------------------------------------------
