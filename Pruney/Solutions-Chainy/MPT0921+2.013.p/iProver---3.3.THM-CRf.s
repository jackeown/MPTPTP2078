%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:24 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  113 (10500 expanded)
%              Number of clauses        :   76 (3965 expanded)
%              Number of leaves         :   11 (2830 expanded)
%              Depth                    :   38
%              Number of atoms          :  639 (88298 expanded)
%              Number of equality atoms :  520 (56358 expanded)
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
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
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
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f18,plain,
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
   => ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK8 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != sK9
                      | ~ m1_subset_1(X9,sK7) )
                  | ~ m1_subset_1(X8,sK6) )
              | ~ m1_subset_1(X7,sK5) )
          | ~ m1_subset_1(X6,sK4) )
      & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK8 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != sK9
                    | ~ m1_subset_1(X9,sK7) )
                | ~ m1_subset_1(X8,sK6) )
            | ~ m1_subset_1(X7,sK5) )
        | ~ m1_subset_1(X6,sK4) )
    & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f12,f18])).

fof(f34,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
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

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f16,plain,(
    ! [X6,X8,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( X4 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X5
          & m1_subset_1(X9,X3) )
     => ( X4 != X6
        & k4_mcart_1(X6,X7,X8,sK3(X0,X1,X2,X3,X4,X5)) = X5
        & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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

fof(f14,plain,(
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

fof(f13,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f16,f15,f14,f13])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X8
      | k4_mcart_1(X6,X7,X8,X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f26])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_451,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK0(X1,X2,X3,X4,X5,X0),X1)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_453,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2,X3,X5,X4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK1(X1,X2,X3,X4,X5,X0),X2)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_454,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X3,X5,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK2(X1,X2,X3,X4,X5,X0),X3)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_455,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2,X3,X5,X4),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(sK3(X1,X2,X3,X4,X5,X0),X4)
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_456,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2,X3,X5,X4),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = X5
    | k4_mcart_1(sK0(X1,X2,X3,X4,X5,X0),sK1(X1,X2,X3,X4,X5,X0),sK2(X1,X2,X3,X4,X5,X0),sK3(X1,X2,X3,X4,X5,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_457,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
    | k4_mcart_1(sK0(X0,X1,X2,X3,X5,X4),sK1(X0,X1,X2,X3,X5,X4),sK2(X0,X1,X2,X3,X5,X4),sK3(X0,X1,X2,X3,X5,X4)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3358,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK2(sK4,sK5,sK6,sK7,X0,sK9),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_457])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_463,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1415,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_463])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f39])).

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

cnf(c_2139,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1415,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_3465,plain,
    ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK2(sK4,sK5,sK6,sK7,X0,sK9),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3358,c_2139])).

cnf(c_3681,plain,
    ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK2(sK4,sK5,sK6,sK7,X0,sK9),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3465,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ m1_subset_1(X1,sK6)
    | ~ m1_subset_1(X2,sK5)
    | ~ m1_subset_1(X3,sK4)
    | k4_mcart_1(X3,X2,X1,X0) != sK9
    | sK8 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_452,plain,
    ( k4_mcart_1(X0,X1,X2,X3) != sK9
    | sK8 = X2
    | m1_subset_1(X3,sK7) != iProver_top
    | m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3686,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_452])).

cnf(c_3773,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_456,c_3686])).

cnf(c_3774,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3773,c_2139])).

cnf(c_21,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3999,plain,
    ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3774,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_4000,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3999])).

cnf(c_4010,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_455,c_4000])).

cnf(c_4011,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4010,c_2139])).

cnf(c_4016,plain,
    ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4011,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_4017,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4016])).

cnf(c_4026,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_4017])).

cnf(c_4027,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4026,c_2139])).

cnf(c_4312,plain,
    ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4027,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_4313,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4312])).

cnf(c_4321,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_4313])).

cnf(c_4322,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4321,c_2139])).

cnf(c_4327,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_4328,plain,
    ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(renaming,[status(thm)],[c_4327])).

cnf(c_4333,plain,
    ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(superposition,[status(thm)],[c_4328,c_3681])).

cnf(c_4,plain,
    ( ~ m1_subset_1(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    | k11_mcart_1(X4,X5,X6,X7,k4_mcart_1(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_462,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4398,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK3(sK4,sK5,sK6,sK7,X4,sK9)
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4333,c_462])).

cnf(c_4667,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK3(sK4,sK5,sK6,sK7,X0,sK9)
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_4398])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_465,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1233,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_465])).

cnf(c_1782,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1233,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_14,negated_conjecture,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1785,plain,
    ( k2_mcart_1(k1_mcart_1(sK9)) != sK8 ),
    inference(demodulation,[status(thm)],[c_1782,c_14])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    | k10_mcart_1(X4,X5,X6,X7,k4_mcart_1(X0,X1,X2,X3)) = X2
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_461,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4399,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4333,c_461])).

cnf(c_4621,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_4399])).

cnf(c_4651,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4621,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715])).

cnf(c_4656,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(superposition,[status(thm)],[c_4333,c_4651])).

cnf(c_4657,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
    | k2_mcart_1(k1_mcart_1(sK9)) = sK8 ),
    inference(demodulation,[status(thm)],[c_4656,c_1782])).

cnf(c_4669,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4667,c_1785,c_4657])).

cnf(c_4864,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_4669,c_4669])).

cnf(c_4985,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_4864,c_18])).

cnf(c_4987,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4985,c_4864])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:24:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.84/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/0.97  
% 2.84/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/0.97  
% 2.84/0.97  ------  iProver source info
% 2.84/0.97  
% 2.84/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.84/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/0.97  git: non_committed_changes: false
% 2.84/0.97  git: last_make_outside_of_git: false
% 2.84/0.97  
% 2.84/0.97  ------ 
% 2.84/0.97  
% 2.84/0.97  ------ Input Options
% 2.84/0.97  
% 2.84/0.97  --out_options                           all
% 2.84/0.97  --tptp_safe_out                         true
% 2.84/0.97  --problem_path                          ""
% 2.84/0.97  --include_path                          ""
% 2.84/0.97  --clausifier                            res/vclausify_rel
% 2.84/0.97  --clausifier_options                    --mode clausify
% 2.84/0.97  --stdin                                 false
% 2.84/0.97  --stats_out                             all
% 2.84/0.97  
% 2.84/0.97  ------ General Options
% 2.84/0.97  
% 2.84/0.97  --fof                                   false
% 2.84/0.97  --time_out_real                         305.
% 2.84/0.97  --time_out_virtual                      -1.
% 2.84/0.97  --symbol_type_check                     false
% 2.84/0.97  --clausify_out                          false
% 2.84/0.97  --sig_cnt_out                           false
% 2.84/0.97  --trig_cnt_out                          false
% 2.84/0.97  --trig_cnt_out_tolerance                1.
% 2.84/0.97  --trig_cnt_out_sk_spl                   false
% 2.84/0.97  --abstr_cl_out                          false
% 2.84/0.97  
% 2.84/0.97  ------ Global Options
% 2.84/0.97  
% 2.84/0.97  --schedule                              default
% 2.84/0.97  --add_important_lit                     false
% 2.84/0.97  --prop_solver_per_cl                    1000
% 2.84/0.97  --min_unsat_core                        false
% 2.84/0.97  --soft_assumptions                      false
% 2.84/0.97  --soft_lemma_size                       3
% 2.84/0.97  --prop_impl_unit_size                   0
% 2.84/0.97  --prop_impl_unit                        []
% 2.84/0.97  --share_sel_clauses                     true
% 2.84/0.97  --reset_solvers                         false
% 2.84/0.97  --bc_imp_inh                            [conj_cone]
% 2.84/0.97  --conj_cone_tolerance                   3.
% 2.84/0.97  --extra_neg_conj                        none
% 2.84/0.97  --large_theory_mode                     true
% 2.84/0.97  --prolific_symb_bound                   200
% 2.84/0.97  --lt_threshold                          2000
% 2.84/0.97  --clause_weak_htbl                      true
% 2.84/0.97  --gc_record_bc_elim                     false
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing Options
% 2.84/0.98  
% 2.84/0.98  --preprocessing_flag                    true
% 2.84/0.98  --time_out_prep_mult                    0.1
% 2.84/0.98  --splitting_mode                        input
% 2.84/0.98  --splitting_grd                         true
% 2.84/0.98  --splitting_cvd                         false
% 2.84/0.98  --splitting_cvd_svl                     false
% 2.84/0.98  --splitting_nvd                         32
% 2.84/0.98  --sub_typing                            true
% 2.84/0.98  --prep_gs_sim                           true
% 2.84/0.98  --prep_unflatten                        true
% 2.84/0.98  --prep_res_sim                          true
% 2.84/0.98  --prep_upred                            true
% 2.84/0.98  --prep_sem_filter                       exhaustive
% 2.84/0.98  --prep_sem_filter_out                   false
% 2.84/0.98  --pred_elim                             true
% 2.84/0.98  --res_sim_input                         true
% 2.84/0.98  --eq_ax_congr_red                       true
% 2.84/0.98  --pure_diseq_elim                       true
% 2.84/0.98  --brand_transform                       false
% 2.84/0.98  --non_eq_to_eq                          false
% 2.84/0.98  --prep_def_merge                        true
% 2.84/0.98  --prep_def_merge_prop_impl              false
% 2.84/0.98  --prep_def_merge_mbd                    true
% 2.84/0.98  --prep_def_merge_tr_red                 false
% 2.84/0.98  --prep_def_merge_tr_cl                  false
% 2.84/0.98  --smt_preprocessing                     true
% 2.84/0.98  --smt_ac_axioms                         fast
% 2.84/0.98  --preprocessed_out                      false
% 2.84/0.98  --preprocessed_stats                    false
% 2.84/0.98  
% 2.84/0.98  ------ Abstraction refinement Options
% 2.84/0.98  
% 2.84/0.98  --abstr_ref                             []
% 2.84/0.98  --abstr_ref_prep                        false
% 2.84/0.98  --abstr_ref_until_sat                   false
% 2.84/0.98  --abstr_ref_sig_restrict                funpre
% 2.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.98  --abstr_ref_under                       []
% 2.84/0.98  
% 2.84/0.98  ------ SAT Options
% 2.84/0.98  
% 2.84/0.98  --sat_mode                              false
% 2.84/0.98  --sat_fm_restart_options                ""
% 2.84/0.98  --sat_gr_def                            false
% 2.84/0.98  --sat_epr_types                         true
% 2.84/0.98  --sat_non_cyclic_types                  false
% 2.84/0.98  --sat_finite_models                     false
% 2.84/0.98  --sat_fm_lemmas                         false
% 2.84/0.98  --sat_fm_prep                           false
% 2.84/0.98  --sat_fm_uc_incr                        true
% 2.84/0.98  --sat_out_model                         small
% 2.84/0.98  --sat_out_clauses                       false
% 2.84/0.98  
% 2.84/0.98  ------ QBF Options
% 2.84/0.98  
% 2.84/0.98  --qbf_mode                              false
% 2.84/0.98  --qbf_elim_univ                         false
% 2.84/0.98  --qbf_dom_inst                          none
% 2.84/0.98  --qbf_dom_pre_inst                      false
% 2.84/0.98  --qbf_sk_in                             false
% 2.84/0.98  --qbf_pred_elim                         true
% 2.84/0.98  --qbf_split                             512
% 2.84/0.98  
% 2.84/0.98  ------ BMC1 Options
% 2.84/0.98  
% 2.84/0.98  --bmc1_incremental                      false
% 2.84/0.98  --bmc1_axioms                           reachable_all
% 2.84/0.98  --bmc1_min_bound                        0
% 2.84/0.98  --bmc1_max_bound                        -1
% 2.84/0.98  --bmc1_max_bound_default                -1
% 2.84/0.98  --bmc1_symbol_reachability              true
% 2.84/0.98  --bmc1_property_lemmas                  false
% 2.84/0.98  --bmc1_k_induction                      false
% 2.84/0.98  --bmc1_non_equiv_states                 false
% 2.84/0.98  --bmc1_deadlock                         false
% 2.84/0.98  --bmc1_ucm                              false
% 2.84/0.98  --bmc1_add_unsat_core                   none
% 2.84/0.98  --bmc1_unsat_core_children              false
% 2.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.98  --bmc1_out_stat                         full
% 2.84/0.98  --bmc1_ground_init                      false
% 2.84/0.98  --bmc1_pre_inst_next_state              false
% 2.84/0.98  --bmc1_pre_inst_state                   false
% 2.84/0.98  --bmc1_pre_inst_reach_state             false
% 2.84/0.98  --bmc1_out_unsat_core                   false
% 2.84/0.98  --bmc1_aig_witness_out                  false
% 2.84/0.98  --bmc1_verbose                          false
% 2.84/0.98  --bmc1_dump_clauses_tptp                false
% 2.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.98  --bmc1_dump_file                        -
% 2.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.98  --bmc1_ucm_extend_mode                  1
% 2.84/0.98  --bmc1_ucm_init_mode                    2
% 2.84/0.98  --bmc1_ucm_cone_mode                    none
% 2.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.98  --bmc1_ucm_relax_model                  4
% 2.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.98  --bmc1_ucm_layered_model                none
% 2.84/0.98  --bmc1_ucm_max_lemma_size               10
% 2.84/0.98  
% 2.84/0.98  ------ AIG Options
% 2.84/0.98  
% 2.84/0.98  --aig_mode                              false
% 2.84/0.98  
% 2.84/0.98  ------ Instantiation Options
% 2.84/0.98  
% 2.84/0.98  --instantiation_flag                    true
% 2.84/0.98  --inst_sos_flag                         false
% 2.84/0.98  --inst_sos_phase                        true
% 2.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel_side                     num_symb
% 2.84/0.98  --inst_solver_per_active                1400
% 2.84/0.98  --inst_solver_calls_frac                1.
% 2.84/0.98  --inst_passive_queue_type               priority_queues
% 2.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.98  --inst_passive_queues_freq              [25;2]
% 2.84/0.98  --inst_dismatching                      true
% 2.84/0.98  --inst_eager_unprocessed_to_passive     true
% 2.84/0.98  --inst_prop_sim_given                   true
% 2.84/0.98  --inst_prop_sim_new                     false
% 2.84/0.98  --inst_subs_new                         false
% 2.84/0.98  --inst_eq_res_simp                      false
% 2.84/0.98  --inst_subs_given                       false
% 2.84/0.98  --inst_orphan_elimination               true
% 2.84/0.98  --inst_learning_loop_flag               true
% 2.84/0.98  --inst_learning_start                   3000
% 2.84/0.98  --inst_learning_factor                  2
% 2.84/0.98  --inst_start_prop_sim_after_learn       3
% 2.84/0.98  --inst_sel_renew                        solver
% 2.84/0.98  --inst_lit_activity_flag                true
% 2.84/0.98  --inst_restr_to_given                   false
% 2.84/0.98  --inst_activity_threshold               500
% 2.84/0.98  --inst_out_proof                        true
% 2.84/0.98  
% 2.84/0.98  ------ Resolution Options
% 2.84/0.98  
% 2.84/0.98  --resolution_flag                       true
% 2.84/0.98  --res_lit_sel                           adaptive
% 2.84/0.98  --res_lit_sel_side                      none
% 2.84/0.98  --res_ordering                          kbo
% 2.84/0.98  --res_to_prop_solver                    active
% 2.84/0.98  --res_prop_simpl_new                    false
% 2.84/0.98  --res_prop_simpl_given                  true
% 2.84/0.98  --res_passive_queue_type                priority_queues
% 2.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.98  --res_passive_queues_freq               [15;5]
% 2.84/0.98  --res_forward_subs                      full
% 2.84/0.98  --res_backward_subs                     full
% 2.84/0.98  --res_forward_subs_resolution           true
% 2.84/0.98  --res_backward_subs_resolution          true
% 2.84/0.98  --res_orphan_elimination                true
% 2.84/0.98  --res_time_limit                        2.
% 2.84/0.98  --res_out_proof                         true
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Options
% 2.84/0.98  
% 2.84/0.98  --superposition_flag                    true
% 2.84/0.98  --sup_passive_queue_type                priority_queues
% 2.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.98  --demod_completeness_check              fast
% 2.84/0.98  --demod_use_ground                      true
% 2.84/0.98  --sup_to_prop_solver                    passive
% 2.84/0.98  --sup_prop_simpl_new                    true
% 2.84/0.98  --sup_prop_simpl_given                  true
% 2.84/0.98  --sup_fun_splitting                     false
% 2.84/0.98  --sup_smt_interval                      50000
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Simplification Setup
% 2.84/0.98  
% 2.84/0.98  --sup_indices_passive                   []
% 2.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_full_bw                           [BwDemod]
% 2.84/0.98  --sup_immed_triv                        [TrivRules]
% 2.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_immed_bw_main                     []
% 2.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  
% 2.84/0.98  ------ Combination Options
% 2.84/0.98  
% 2.84/0.98  --comb_res_mult                         3
% 2.84/0.98  --comb_sup_mult                         2
% 2.84/0.98  --comb_inst_mult                        10
% 2.84/0.98  
% 2.84/0.98  ------ Debug Options
% 2.84/0.98  
% 2.84/0.98  --dbg_backtrace                         false
% 2.84/0.98  --dbg_dump_prop_clauses                 false
% 2.84/0.98  --dbg_dump_prop_clauses_file            -
% 2.84/0.98  --dbg_out_stat                          false
% 2.84/0.98  ------ Parsing...
% 2.84/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/0.98  ------ Proving...
% 2.84/0.98  ------ Problem Properties 
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  clauses                                 21
% 2.84/0.98  conjectures                             7
% 2.84/0.98  EPR                                     4
% 2.84/0.98  Horn                                    7
% 2.84/0.98  unary                                   6
% 2.84/0.98  binary                                  0
% 2.84/0.98  lits                                    102
% 2.84/0.98  lits eq                                 79
% 2.84/0.98  fd_pure                                 0
% 2.84/0.98  fd_pseudo                               0
% 2.84/0.98  fd_cond                                 5
% 2.84/0.98  fd_pseudo_cond                          5
% 2.84/0.98  AC symbols                              0
% 2.84/0.98  
% 2.84/0.98  ------ Schedule dynamic 5 is on 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  ------ 
% 2.84/0.98  Current options:
% 2.84/0.98  ------ 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options
% 2.84/0.98  
% 2.84/0.98  --out_options                           all
% 2.84/0.98  --tptp_safe_out                         true
% 2.84/0.98  --problem_path                          ""
% 2.84/0.98  --include_path                          ""
% 2.84/0.98  --clausifier                            res/vclausify_rel
% 2.84/0.98  --clausifier_options                    --mode clausify
% 2.84/0.98  --stdin                                 false
% 2.84/0.98  --stats_out                             all
% 2.84/0.98  
% 2.84/0.98  ------ General Options
% 2.84/0.98  
% 2.84/0.98  --fof                                   false
% 2.84/0.98  --time_out_real                         305.
% 2.84/0.98  --time_out_virtual                      -1.
% 2.84/0.98  --symbol_type_check                     false
% 2.84/0.98  --clausify_out                          false
% 2.84/0.98  --sig_cnt_out                           false
% 2.84/0.98  --trig_cnt_out                          false
% 2.84/0.98  --trig_cnt_out_tolerance                1.
% 2.84/0.98  --trig_cnt_out_sk_spl                   false
% 2.84/0.98  --abstr_cl_out                          false
% 2.84/0.98  
% 2.84/0.98  ------ Global Options
% 2.84/0.98  
% 2.84/0.98  --schedule                              default
% 2.84/0.98  --add_important_lit                     false
% 2.84/0.98  --prop_solver_per_cl                    1000
% 2.84/0.98  --min_unsat_core                        false
% 2.84/0.98  --soft_assumptions                      false
% 2.84/0.98  --soft_lemma_size                       3
% 2.84/0.98  --prop_impl_unit_size                   0
% 2.84/0.98  --prop_impl_unit                        []
% 2.84/0.98  --share_sel_clauses                     true
% 2.84/0.98  --reset_solvers                         false
% 2.84/0.98  --bc_imp_inh                            [conj_cone]
% 2.84/0.98  --conj_cone_tolerance                   3.
% 2.84/0.98  --extra_neg_conj                        none
% 2.84/0.98  --large_theory_mode                     true
% 2.84/0.98  --prolific_symb_bound                   200
% 2.84/0.98  --lt_threshold                          2000
% 2.84/0.98  --clause_weak_htbl                      true
% 2.84/0.98  --gc_record_bc_elim                     false
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing Options
% 2.84/0.98  
% 2.84/0.98  --preprocessing_flag                    true
% 2.84/0.98  --time_out_prep_mult                    0.1
% 2.84/0.98  --splitting_mode                        input
% 2.84/0.98  --splitting_grd                         true
% 2.84/0.98  --splitting_cvd                         false
% 2.84/0.98  --splitting_cvd_svl                     false
% 2.84/0.98  --splitting_nvd                         32
% 2.84/0.98  --sub_typing                            true
% 2.84/0.98  --prep_gs_sim                           true
% 2.84/0.98  --prep_unflatten                        true
% 2.84/0.98  --prep_res_sim                          true
% 2.84/0.98  --prep_upred                            true
% 2.84/0.98  --prep_sem_filter                       exhaustive
% 2.84/0.98  --prep_sem_filter_out                   false
% 2.84/0.98  --pred_elim                             true
% 2.84/0.98  --res_sim_input                         true
% 2.84/0.98  --eq_ax_congr_red                       true
% 2.84/0.98  --pure_diseq_elim                       true
% 2.84/0.98  --brand_transform                       false
% 2.84/0.98  --non_eq_to_eq                          false
% 2.84/0.98  --prep_def_merge                        true
% 2.84/0.98  --prep_def_merge_prop_impl              false
% 2.84/0.98  --prep_def_merge_mbd                    true
% 2.84/0.98  --prep_def_merge_tr_red                 false
% 2.84/0.98  --prep_def_merge_tr_cl                  false
% 2.84/0.98  --smt_preprocessing                     true
% 2.84/0.98  --smt_ac_axioms                         fast
% 2.84/0.98  --preprocessed_out                      false
% 2.84/0.98  --preprocessed_stats                    false
% 2.84/0.98  
% 2.84/0.98  ------ Abstraction refinement Options
% 2.84/0.98  
% 2.84/0.98  --abstr_ref                             []
% 2.84/0.98  --abstr_ref_prep                        false
% 2.84/0.98  --abstr_ref_until_sat                   false
% 2.84/0.98  --abstr_ref_sig_restrict                funpre
% 2.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.98  --abstr_ref_under                       []
% 2.84/0.98  
% 2.84/0.98  ------ SAT Options
% 2.84/0.98  
% 2.84/0.98  --sat_mode                              false
% 2.84/0.98  --sat_fm_restart_options                ""
% 2.84/0.98  --sat_gr_def                            false
% 2.84/0.98  --sat_epr_types                         true
% 2.84/0.98  --sat_non_cyclic_types                  false
% 2.84/0.98  --sat_finite_models                     false
% 2.84/0.98  --sat_fm_lemmas                         false
% 2.84/0.98  --sat_fm_prep                           false
% 2.84/0.98  --sat_fm_uc_incr                        true
% 2.84/0.98  --sat_out_model                         small
% 2.84/0.98  --sat_out_clauses                       false
% 2.84/0.98  
% 2.84/0.98  ------ QBF Options
% 2.84/0.98  
% 2.84/0.98  --qbf_mode                              false
% 2.84/0.98  --qbf_elim_univ                         false
% 2.84/0.98  --qbf_dom_inst                          none
% 2.84/0.98  --qbf_dom_pre_inst                      false
% 2.84/0.98  --qbf_sk_in                             false
% 2.84/0.98  --qbf_pred_elim                         true
% 2.84/0.98  --qbf_split                             512
% 2.84/0.98  
% 2.84/0.98  ------ BMC1 Options
% 2.84/0.98  
% 2.84/0.98  --bmc1_incremental                      false
% 2.84/0.98  --bmc1_axioms                           reachable_all
% 2.84/0.98  --bmc1_min_bound                        0
% 2.84/0.98  --bmc1_max_bound                        -1
% 2.84/0.98  --bmc1_max_bound_default                -1
% 2.84/0.98  --bmc1_symbol_reachability              true
% 2.84/0.98  --bmc1_property_lemmas                  false
% 2.84/0.98  --bmc1_k_induction                      false
% 2.84/0.98  --bmc1_non_equiv_states                 false
% 2.84/0.98  --bmc1_deadlock                         false
% 2.84/0.98  --bmc1_ucm                              false
% 2.84/0.98  --bmc1_add_unsat_core                   none
% 2.84/0.98  --bmc1_unsat_core_children              false
% 2.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.98  --bmc1_out_stat                         full
% 2.84/0.98  --bmc1_ground_init                      false
% 2.84/0.98  --bmc1_pre_inst_next_state              false
% 2.84/0.98  --bmc1_pre_inst_state                   false
% 2.84/0.98  --bmc1_pre_inst_reach_state             false
% 2.84/0.98  --bmc1_out_unsat_core                   false
% 2.84/0.98  --bmc1_aig_witness_out                  false
% 2.84/0.98  --bmc1_verbose                          false
% 2.84/0.98  --bmc1_dump_clauses_tptp                false
% 2.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.98  --bmc1_dump_file                        -
% 2.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.98  --bmc1_ucm_extend_mode                  1
% 2.84/0.98  --bmc1_ucm_init_mode                    2
% 2.84/0.98  --bmc1_ucm_cone_mode                    none
% 2.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.98  --bmc1_ucm_relax_model                  4
% 2.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.98  --bmc1_ucm_layered_model                none
% 2.84/0.98  --bmc1_ucm_max_lemma_size               10
% 2.84/0.98  
% 2.84/0.98  ------ AIG Options
% 2.84/0.98  
% 2.84/0.98  --aig_mode                              false
% 2.84/0.98  
% 2.84/0.98  ------ Instantiation Options
% 2.84/0.98  
% 2.84/0.98  --instantiation_flag                    true
% 2.84/0.98  --inst_sos_flag                         false
% 2.84/0.98  --inst_sos_phase                        true
% 2.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel_side                     none
% 2.84/0.98  --inst_solver_per_active                1400
% 2.84/0.98  --inst_solver_calls_frac                1.
% 2.84/0.98  --inst_passive_queue_type               priority_queues
% 2.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.98  --inst_passive_queues_freq              [25;2]
% 2.84/0.98  --inst_dismatching                      true
% 2.84/0.98  --inst_eager_unprocessed_to_passive     true
% 2.84/0.98  --inst_prop_sim_given                   true
% 2.84/0.98  --inst_prop_sim_new                     false
% 2.84/0.98  --inst_subs_new                         false
% 2.84/0.98  --inst_eq_res_simp                      false
% 2.84/0.98  --inst_subs_given                       false
% 2.84/0.98  --inst_orphan_elimination               true
% 2.84/0.98  --inst_learning_loop_flag               true
% 2.84/0.98  --inst_learning_start                   3000
% 2.84/0.98  --inst_learning_factor                  2
% 2.84/0.98  --inst_start_prop_sim_after_learn       3
% 2.84/0.98  --inst_sel_renew                        solver
% 2.84/0.98  --inst_lit_activity_flag                true
% 2.84/0.98  --inst_restr_to_given                   false
% 2.84/0.98  --inst_activity_threshold               500
% 2.84/0.98  --inst_out_proof                        true
% 2.84/0.98  
% 2.84/0.98  ------ Resolution Options
% 2.84/0.98  
% 2.84/0.98  --resolution_flag                       false
% 2.84/0.98  --res_lit_sel                           adaptive
% 2.84/0.98  --res_lit_sel_side                      none
% 2.84/0.98  --res_ordering                          kbo
% 2.84/0.98  --res_to_prop_solver                    active
% 2.84/0.98  --res_prop_simpl_new                    false
% 2.84/0.98  --res_prop_simpl_given                  true
% 2.84/0.98  --res_passive_queue_type                priority_queues
% 2.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.98  --res_passive_queues_freq               [15;5]
% 2.84/0.98  --res_forward_subs                      full
% 2.84/0.98  --res_backward_subs                     full
% 2.84/0.98  --res_forward_subs_resolution           true
% 2.84/0.98  --res_backward_subs_resolution          true
% 2.84/0.98  --res_orphan_elimination                true
% 2.84/0.98  --res_time_limit                        2.
% 2.84/0.98  --res_out_proof                         true
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Options
% 2.84/0.98  
% 2.84/0.98  --superposition_flag                    true
% 2.84/0.98  --sup_passive_queue_type                priority_queues
% 2.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.98  --demod_completeness_check              fast
% 2.84/0.98  --demod_use_ground                      true
% 2.84/0.98  --sup_to_prop_solver                    passive
% 2.84/0.98  --sup_prop_simpl_new                    true
% 2.84/0.98  --sup_prop_simpl_given                  true
% 2.84/0.98  --sup_fun_splitting                     false
% 2.84/0.98  --sup_smt_interval                      50000
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Simplification Setup
% 2.84/0.98  
% 2.84/0.98  --sup_indices_passive                   []
% 2.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_full_bw                           [BwDemod]
% 2.84/0.98  --sup_immed_triv                        [TrivRules]
% 2.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_immed_bw_main                     []
% 2.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  
% 2.84/0.98  ------ Combination Options
% 2.84/0.98  
% 2.84/0.98  --comb_res_mult                         3
% 2.84/0.98  --comb_sup_mult                         2
% 2.84/0.98  --comb_inst_mult                        10
% 2.84/0.98  
% 2.84/0.98  ------ Debug Options
% 2.84/0.98  
% 2.84/0.98  --dbg_backtrace                         false
% 2.84/0.98  --dbg_dump_prop_clauses                 false
% 2.84/0.98  --dbg_dump_prop_clauses_file            -
% 2.84/0.98  --dbg_out_stat                          false
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  ------ Proving...
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  % SZS status Theorem for theBenchmark.p
% 2.84/0.98  
% 2.84/0.98   Resolution empty clause
% 2.84/0.98  
% 2.84/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  fof(f4,conjecture,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f5,negated_conjecture,(
% 2.84/0.98    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.84/0.98    inference(negated_conjecture,[],[f4])).
% 2.84/0.98  
% 2.84/0.98  fof(f11,plain,(
% 2.84/0.98    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.84/0.98    inference(ennf_transformation,[],[f5])).
% 2.84/0.98  
% 2.84/0.98  fof(f12,plain,(
% 2.84/0.98    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.84/0.98    inference(flattening,[],[f11])).
% 2.84/0.98  
% 2.84/0.98  fof(f18,plain,(
% 2.84/0.98    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f19,plain,(
% 2.84/0.98    k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.84/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f12,f18])).
% 2.84/0.98  
% 2.84/0.98  fof(f34,plain,(
% 2.84/0.98    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.84/0.98    inference(cnf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f3,axiom,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f9,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.84/0.98    inference(ennf_transformation,[],[f3])).
% 2.84/0.98  
% 2.84/0.98  fof(f10,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.84/0.98    inference(flattening,[],[f9])).
% 2.84/0.98  
% 2.84/0.98  fof(f16,plain,(
% 2.84/0.98    ( ! [X6,X8,X7] : (! [X5,X4,X3,X2,X1,X0] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) => (X4 != X6 & k4_mcart_1(X6,X7,X8,sK3(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)))) )),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f15,plain,(
% 2.84/0.98    ( ! [X6,X7] : (! [X5,X4,X3,X2,X1,X0] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) => (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,sK2(X0,X1,X2,X3,X4,X5),X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)))) )),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f14,plain,(
% 2.84/0.98    ( ! [X6] : (! [X5,X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) => (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,sK1(X0,X1,X2,X3,X4,X5),X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)))) )),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f13,plain,(
% 2.84/0.98    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) => (? [X7] : (? [X8] : (? [X9] : (sK0(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)))),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f17,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ((((sK0(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.84/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f16,f15,f14,f13])).
% 2.84/0.98  
% 2.84/0.98  fof(f28,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f17])).
% 2.84/0.98  
% 2.84/0.98  fof(f29,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f17])).
% 2.84/0.98  
% 2.84/0.98  fof(f30,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f17])).
% 2.84/0.98  
% 2.84/0.98  fof(f31,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK3(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f17])).
% 2.84/0.98  
% 2.84/0.98  fof(f32,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_mcart_1(sK0(X0,X1,X2,X3,X4,X5),sK1(X0,X1,X2,X3,X4,X5),sK2(X0,X1,X2,X3,X4,X5),sK3(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f17])).
% 2.84/0.98  
% 2.84/0.98  fof(f1,axiom,(
% 2.84/0.98    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f6,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.84/0.98    inference(ennf_transformation,[],[f1])).
% 2.84/0.98  
% 2.84/0.98  fof(f20,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.84/0.98    inference(cnf_transformation,[],[f6])).
% 2.84/0.98  
% 2.84/0.98  fof(f36,plain,(
% 2.84/0.98    k1_xboole_0 != sK4),
% 2.84/0.98    inference(cnf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f37,plain,(
% 2.84/0.98    k1_xboole_0 != sK5),
% 2.84/0.98    inference(cnf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f38,plain,(
% 2.84/0.98    k1_xboole_0 != sK6),
% 2.84/0.98    inference(cnf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f39,plain,(
% 2.84/0.98    k1_xboole_0 != sK7),
% 2.84/0.98    inference(cnf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f35,plain,(
% 2.84/0.98    ( ! [X6,X8,X7,X9] : (sK8 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f2,axiom,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 2.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f7,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.84/0.98    inference(ennf_transformation,[],[f2])).
% 2.84/0.98  
% 2.84/0.98  fof(f8,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.84/0.98    inference(flattening,[],[f7])).
% 2.84/0.98  
% 2.84/0.98  fof(f27,plain,(
% 2.84/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f8])).
% 2.84/0.98  
% 2.84/0.98  fof(f41,plain,(
% 2.84/0.98    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(equality_resolution,[],[f27])).
% 2.84/0.98  
% 2.84/0.98  fof(f22,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.84/0.98    inference(cnf_transformation,[],[f6])).
% 2.84/0.98  
% 2.84/0.98  fof(f40,plain,(
% 2.84/0.98    k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8),
% 2.84/0.98    inference(cnf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f26,plain,(
% 2.84/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f8])).
% 2.84/0.98  
% 2.84/0.98  fof(f42,plain,(
% 2.84/0.98    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.84/0.98    inference(equality_resolution,[],[f26])).
% 2.84/0.98  
% 2.84/0.98  cnf(c_20,negated_conjecture,
% 2.84/0.98      ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_451,plain,
% 2.84/0.98      ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_13,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.84/0.98      | m1_subset_1(sK0(X1,X2,X3,X4,X5,X0),X1)
% 2.84/0.98      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.84/0.98      | k1_xboole_0 = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_453,plain,
% 2.84/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(X0,X1,X2,X3,X5,X4),X0) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_12,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.84/0.98      | m1_subset_1(sK1(X1,X2,X3,X4,X5,X0),X2)
% 2.84/0.98      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.84/0.98      | k1_xboole_0 = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_454,plain,
% 2.84/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
% 2.84/0.98      | m1_subset_1(sK1(X0,X1,X2,X3,X5,X4),X1) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_11,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.84/0.98      | m1_subset_1(sK2(X1,X2,X3,X4,X5,X0),X3)
% 2.84/0.98      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.84/0.98      | k1_xboole_0 = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_455,plain,
% 2.84/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
% 2.84/0.98      | m1_subset_1(sK2(X0,X1,X2,X3,X5,X4),X2) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_10,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.84/0.98      | m1_subset_1(sK3(X1,X2,X3,X4,X5,X0),X4)
% 2.84/0.98      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.84/0.98      | k1_xboole_0 = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_456,plain,
% 2.84/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
% 2.84/0.98      | m1_subset_1(sK3(X0,X1,X2,X3,X5,X4),X3) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_9,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.84/0.98      | k8_mcart_1(X1,X2,X3,X4,X0) = X5
% 2.84/0.98      | k4_mcart_1(sK0(X1,X2,X3,X4,X5,X0),sK1(X1,X2,X3,X4,X5,X0),sK2(X1,X2,X3,X4,X5,X0),sK3(X1,X2,X3,X4,X5,X0)) = X0
% 2.84/0.98      | k1_xboole_0 = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_457,plain,
% 2.84/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
% 2.84/0.98      | k4_mcart_1(sK0(X0,X1,X2,X3,X5,X4),sK1(X0,X1,X2,X3,X5,X4),sK2(X0,X1,X2,X3,X5,X4),sK3(X0,X1,X2,X3,X5,X4)) = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3358,plain,
% 2.84/0.98      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.84/0.98      | k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK2(sK4,sK5,sK6,sK7,X0,sK9),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_451,c_457]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.84/0.98      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.84/0.98      | k1_xboole_0 = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f20]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_463,plain,
% 2.84/0.98      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1415,plain,
% 2.84/0.98      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_451,c_463]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_18,negated_conjecture,
% 2.84/0.98      ( k1_xboole_0 != sK4 ),
% 2.84/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_17,negated_conjecture,
% 2.84/0.98      ( k1_xboole_0 != sK5 ),
% 2.84/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_16,negated_conjecture,
% 2.84/0.98      ( k1_xboole_0 != sK6 ),
% 2.84/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_15,negated_conjecture,
% 2.84/0.98      ( k1_xboole_0 != sK7 ),
% 2.84/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_192,plain,( X0 = X0 ),theory(equality) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_213,plain,
% 2.84/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_192]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_193,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_708,plain,
% 2.84/0.98      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_193]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_709,plain,
% 2.84/0.98      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_708]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_710,plain,
% 2.84/0.98      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_193]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_711,plain,
% 2.84/0.98      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_710]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_712,plain,
% 2.84/0.98      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_193]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_713,plain,
% 2.84/0.98      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_712]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_714,plain,
% 2.84/0.98      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_193]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_715,plain,
% 2.84/0.98      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_714]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2139,plain,
% 2.84/0.98      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_1415,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3465,plain,
% 2.84/0.98      ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK2(sK4,sK5,sK6,sK7,X0,sK9),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0 ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_3358,c_2139]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3681,plain,
% 2.84/0.98      ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK2(sK4,sK5,sK6,sK7,X0,sK9),sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_3465,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_19,negated_conjecture,
% 2.84/0.98      ( ~ m1_subset_1(X0,sK7)
% 2.84/0.98      | ~ m1_subset_1(X1,sK6)
% 2.84/0.98      | ~ m1_subset_1(X2,sK5)
% 2.84/0.98      | ~ m1_subset_1(X3,sK4)
% 2.84/0.98      | k4_mcart_1(X3,X2,X1,X0) != sK9
% 2.84/0.98      | sK8 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_452,plain,
% 2.84/0.98      ( k4_mcart_1(X0,X1,X2,X3) != sK9
% 2.84/0.98      | sK8 = X2
% 2.84/0.98      | m1_subset_1(X3,sK7) != iProver_top
% 2.84/0.98      | m1_subset_1(X2,sK6) != iProver_top
% 2.84/0.98      | m1_subset_1(X1,sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(X0,sK4) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3686,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,X0,sK9),sK7) != iProver_top
% 2.84/0.98      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_3681,c_452]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3773,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_456,c_3686]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3774,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_3773,c_2139]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_21,plain,
% 2.84/0.98      ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3999,plain,
% 2.84/0.98      ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_3774,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4000,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,X0,sK9),sK6) != iProver_top
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_3999]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4010,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_455,c_4000]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4011,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_4010,c_2139]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4016,plain,
% 2.84/0.98      ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_4011,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4017,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,X0,sK9),sK5) != iProver_top
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_4016]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4026,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_454,c_4017]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4027,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_4026,c_2139]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4312,plain,
% 2.84/0.98      ( m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_4027,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4313,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK4) != iProver_top ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_4312]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4321,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k8_mcart_1(sK4,sK5,sK6,sK7,sK9) = X0
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_453,c_4313]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4322,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_4321,c_2139]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4327,plain,
% 2.84/0.98      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_4322,c_21,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4328,plain,
% 2.84/0.98      ( sK2(sK4,sK5,sK6,sK7,X0,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_4327]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4333,plain,
% 2.84/0.98      ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9)) = sK9
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4328,c_3681]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4,plain,
% 2.84/0.98      ( ~ m1_subset_1(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
% 2.84/0.98      | k11_mcart_1(X4,X5,X6,X7,k4_mcart_1(X0,X1,X2,X3)) = X3
% 2.84/0.98      | k1_xboole_0 = X7
% 2.84/0.98      | k1_xboole_0 = X6
% 2.84/0.98      | k1_xboole_0 = X5
% 2.84/0.98      | k1_xboole_0 = X4 ),
% 2.84/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_462,plain,
% 2.84/0.98      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4398,plain,
% 2.84/0.98      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK3(sK4,sK5,sK6,sK7,X4,sK9)
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4333,c_462]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4667,plain,
% 2.84/0.98      ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK3(sK4,sK5,sK6,sK7,X0,sK9)
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_451,c_4398]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.84/0.98      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.84/0.98      | k1_xboole_0 = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f22]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_465,plain,
% 2.84/0.98      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1233,plain,
% 2.84/0.98      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9))
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_451,c_465]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1782,plain,
% 2.84/0.98      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = k2_mcart_1(k1_mcart_1(sK9)) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_1233,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_14,negated_conjecture,
% 2.84/0.98      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
% 2.84/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1785,plain,
% 2.84/0.98      ( k2_mcart_1(k1_mcart_1(sK9)) != sK8 ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_1782,c_14]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_5,plain,
% 2.84/0.98      ( ~ m1_subset_1(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
% 2.84/0.98      | k10_mcart_1(X4,X5,X6,X7,k4_mcart_1(X0,X1,X2,X3)) = X2
% 2.84/0.98      | k1_xboole_0 = X7
% 2.84/0.98      | k1_xboole_0 = X6
% 2.84/0.98      | k1_xboole_0 = X5
% 2.84/0.98      | k1_xboole_0 = X4 ),
% 2.84/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_461,plain,
% 2.84/0.98      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4399,plain,
% 2.84/0.98      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X4,sK9),sK1(sK4,sK5,sK6,sK7,X4,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X4,sK9))) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X4
% 2.84/0.98      | k1_xboole_0 = X3
% 2.84/0.98      | k1_xboole_0 = X2
% 2.84/0.98      | k1_xboole_0 = X1
% 2.84/0.98      | k1_xboole_0 = X0
% 2.84/0.98      | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4333,c_461]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4621,plain,
% 2.84/0.98      ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | sK7 = k1_xboole_0
% 2.84/0.98      | sK6 = k1_xboole_0
% 2.84/0.98      | sK5 = k1_xboole_0
% 2.84/0.98      | sK4 = k1_xboole_0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_451,c_4399]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4651,plain,
% 2.84/0.98      ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,X0,sK9),sK1(sK4,sK5,sK6,sK7,X0,sK9),sK8,sK3(sK4,sK5,sK6,sK7,X0,sK9))) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_4621,c_18,c_17,c_16,c_15,c_213,c_709,c_711,c_713,c_715]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4656,plain,
% 2.84/0.98      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
% 2.84/0.98      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4333,c_4651]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4657,plain,
% 2.84/0.98      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0
% 2.84/0.98      | k2_mcart_1(k1_mcart_1(sK9)) = sK8 ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_4656,c_1782]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4669,plain,
% 2.84/0.98      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) = X0 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_4667,c_1785,c_4657]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4864,plain,
% 2.84/0.98      ( X0 = X1 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4669,c_4669]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4985,plain,
% 2.84/0.98      ( k1_xboole_0 != X0 ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4864,c_18]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4987,plain,
% 2.84/0.98      ( $false ),
% 2.84/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_4985,c_4864]) ).
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  ------                               Statistics
% 2.84/0.98  
% 2.84/0.98  ------ General
% 2.84/0.98  
% 2.84/0.98  abstr_ref_over_cycles:                  0
% 2.84/0.98  abstr_ref_under_cycles:                 0
% 2.84/0.98  gc_basic_clause_elim:                   0
% 2.84/0.98  forced_gc_time:                         0
% 2.84/0.98  parsing_time:                           0.008
% 2.84/0.98  unif_index_cands_time:                  0.
% 2.84/0.98  unif_index_add_time:                    0.
% 2.84/0.98  orderings_time:                         0.
% 2.84/0.98  out_proof_time:                         0.01
% 2.84/0.98  total_time:                             0.185
% 2.84/0.98  num_of_symbols:                         48
% 2.84/0.98  num_of_terms:                           9929
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing
% 2.84/0.98  
% 2.84/0.98  num_of_splits:                          0
% 2.84/0.98  num_of_split_atoms:                     0
% 2.84/0.98  num_of_reused_defs:                     0
% 2.84/0.98  num_eq_ax_congr_red:                    72
% 2.84/0.98  num_of_sem_filtered_clauses:            1
% 2.84/0.98  num_of_subtypes:                        0
% 2.84/0.98  monotx_restored_types:                  0
% 2.84/0.98  sat_num_of_epr_types:                   0
% 2.84/0.98  sat_num_of_non_cyclic_types:            0
% 2.84/0.98  sat_guarded_non_collapsed_types:        0
% 2.84/0.98  num_pure_diseq_elim:                    0
% 2.84/0.98  simp_replaced_by:                       0
% 2.84/0.98  res_preprocessed:                       86
% 2.84/0.98  prep_upred:                             0
% 2.84/0.98  prep_unflattend:                        0
% 2.84/0.98  smt_new_axioms:                         0
% 2.84/0.98  pred_elim_cands:                        1
% 2.84/0.98  pred_elim:                              0
% 2.84/0.98  pred_elim_cl:                           0
% 2.84/0.98  pred_elim_cycles:                       1
% 2.84/0.98  merged_defs:                            0
% 2.84/0.98  merged_defs_ncl:                        0
% 2.84/0.98  bin_hyper_res:                          0
% 2.84/0.98  prep_cycles:                            3
% 2.84/0.98  pred_elim_time:                         0.
% 2.84/0.98  splitting_time:                         0.
% 2.84/0.98  sem_filter_time:                        0.
% 2.84/0.98  monotx_time:                            0.
% 2.84/0.98  subtype_inf_time:                       0.
% 2.84/0.98  
% 2.84/0.98  ------ Problem properties
% 2.84/0.98  
% 2.84/0.98  clauses:                                21
% 2.84/0.98  conjectures:                            7
% 2.84/0.98  epr:                                    4
% 2.84/0.98  horn:                                   7
% 2.84/0.98  ground:                                 6
% 2.84/0.98  unary:                                  6
% 2.84/0.98  binary:                                 0
% 2.84/0.98  lits:                                   102
% 2.84/0.98  lits_eq:                                79
% 2.84/0.98  fd_pure:                                0
% 2.84/0.98  fd_pseudo:                              0
% 2.84/0.98  fd_cond:                                5
% 2.84/0.98  fd_pseudo_cond:                         5
% 2.84/0.98  ac_symbols:                             0
% 2.84/0.98  
% 2.84/0.98  ------ Propositional Solver
% 2.84/0.98  
% 2.84/0.98  prop_solver_calls:                      22
% 2.84/0.98  prop_fast_solver_calls:                 998
% 2.84/0.98  smt_solver_calls:                       0
% 2.84/0.98  smt_fast_solver_calls:                  0
% 2.84/0.98  prop_num_of_clauses:                    1852
% 2.84/0.98  prop_preprocess_simplified:             6892
% 2.84/0.98  prop_fo_subsumed:                       54
% 2.84/0.98  prop_solver_time:                       0.
% 2.84/0.98  smt_solver_time:                        0.
% 2.84/0.98  smt_fast_solver_time:                   0.
% 2.84/0.98  prop_fast_solver_time:                  0.
% 2.84/0.98  prop_unsat_core_time:                   0.
% 2.84/0.98  
% 2.84/0.98  ------ QBF
% 2.84/0.98  
% 2.84/0.98  qbf_q_res:                              0
% 2.84/0.98  qbf_num_tautologies:                    0
% 2.84/0.98  qbf_prep_cycles:                        0
% 2.84/0.98  
% 2.84/0.98  ------ BMC1
% 2.84/0.98  
% 2.84/0.98  bmc1_current_bound:                     -1
% 2.84/0.98  bmc1_last_solved_bound:                 -1
% 2.84/0.98  bmc1_unsat_core_size:                   -1
% 2.84/0.98  bmc1_unsat_core_parents_size:           -1
% 2.84/0.98  bmc1_merge_next_fun:                    0
% 2.84/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.84/0.98  
% 2.84/0.98  ------ Instantiation
% 2.84/0.98  
% 2.84/0.98  inst_num_of_clauses:                    573
% 2.84/0.98  inst_num_in_passive:                    346
% 2.84/0.98  inst_num_in_active:                     210
% 2.84/0.98  inst_num_in_unprocessed:                17
% 2.84/0.98  inst_num_of_loops:                      210
% 2.84/0.98  inst_num_of_learning_restarts:          0
% 2.84/0.98  inst_num_moves_active_passive:          0
% 2.84/0.98  inst_lit_activity:                      0
% 2.84/0.98  inst_lit_activity_moves:                0
% 2.84/0.98  inst_num_tautologies:                   0
% 2.84/0.98  inst_num_prop_implied:                  0
% 2.84/0.98  inst_num_existing_simplified:           0
% 2.84/0.98  inst_num_eq_res_simplified:             0
% 2.84/0.98  inst_num_child_elim:                    0
% 2.84/0.98  inst_num_of_dismatching_blockings:      0
% 2.84/0.98  inst_num_of_non_proper_insts:           533
% 2.84/0.98  inst_num_of_duplicates:                 0
% 2.84/0.98  inst_inst_num_from_inst_to_res:         0
% 2.84/0.98  inst_dismatching_checking_time:         0.
% 2.84/0.98  
% 2.84/0.98  ------ Resolution
% 2.84/0.98  
% 2.84/0.98  res_num_of_clauses:                     0
% 2.84/0.98  res_num_in_passive:                     0
% 2.84/0.98  res_num_in_active:                      0
% 2.84/0.98  res_num_of_loops:                       89
% 2.84/0.98  res_forward_subset_subsumed:            5
% 2.84/0.98  res_backward_subset_subsumed:           0
% 2.84/0.98  res_forward_subsumed:                   0
% 2.84/0.98  res_backward_subsumed:                  0
% 2.84/0.98  res_forward_subsumption_resolution:     0
% 2.84/0.98  res_backward_subsumption_resolution:    0
% 2.84/0.98  res_clause_to_clause_subsumption:       265
% 2.84/0.98  res_orphan_elimination:                 0
% 2.84/0.98  res_tautology_del:                      0
% 2.84/0.98  res_num_eq_res_simplified:              0
% 2.84/0.98  res_num_sel_changes:                    0
% 2.84/0.98  res_moves_from_active_to_pass:          0
% 2.84/0.98  
% 2.84/0.98  ------ Superposition
% 2.84/0.98  
% 2.84/0.98  sup_time_total:                         0.
% 2.84/0.98  sup_time_generating:                    0.
% 2.84/0.98  sup_time_sim_full:                      0.
% 2.84/0.98  sup_time_sim_immed:                     0.
% 2.84/0.98  
% 2.84/0.98  sup_num_of_clauses:                     53
% 2.84/0.98  sup_num_in_active:                      11
% 2.84/0.98  sup_num_in_passive:                     42
% 2.84/0.98  sup_num_of_loops:                       41
% 2.84/0.98  sup_fw_superposition:                   24
% 2.84/0.98  sup_bw_superposition:                   104
% 2.84/0.98  sup_immediate_simplified:               18
% 2.84/0.98  sup_given_eliminated:                   3
% 2.84/0.98  comparisons_done:                       0
% 2.84/0.98  comparisons_avoided:                    87
% 2.84/0.98  
% 2.84/0.98  ------ Simplifications
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  sim_fw_subset_subsumed:                 8
% 2.84/0.98  sim_bw_subset_subsumed:                 6
% 2.84/0.98  sim_fw_subsumed:                        7
% 2.84/0.98  sim_bw_subsumed:                        1
% 2.84/0.98  sim_fw_subsumption_res:                 1
% 2.84/0.98  sim_bw_subsumption_res:                 0
% 2.84/0.98  sim_tautology_del:                      0
% 2.84/0.98  sim_eq_tautology_del:                   1
% 2.84/0.98  sim_eq_res_simp:                        0
% 2.84/0.98  sim_fw_demodulated:                     7
% 2.84/0.98  sim_bw_demodulated:                     25
% 2.84/0.98  sim_light_normalised:                   0
% 2.84/0.98  sim_joinable_taut:                      0
% 2.84/0.98  sim_joinable_simp:                      0
% 2.84/0.98  sim_ac_normalised:                      0
% 2.84/0.98  sim_smt_subsumption:                    0
% 2.84/0.98  
%------------------------------------------------------------------------------
