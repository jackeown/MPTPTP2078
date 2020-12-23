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
% DateTime   : Thu Dec  3 11:59:23 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 774 expanded)
%              Number of clauses        :   45 ( 209 expanded)
%              Number of leaves         :   12 ( 236 expanded)
%              Depth                    :   17
%              Number of atoms          :  441 (5380 expanded)
%              Number of equality atoms :  325 (3297 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f10])).

fof(f17,plain,
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

fof(f18,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f11,f17])).

fof(f30,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f47,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(X5,X6,X7,X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(X5,X6,X7,sK3(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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

fof(f13,plain,(
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

fof(f12,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f32,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X6,X8,X7,X9] :
      ( sK8 = X8
      | k4_mcart_1(X6,X7,X8,X9) != sK9
      | ~ m1_subset_1(X9,sK7)
      | ~ m1_subset_1(X8,sK6)
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f21,f37])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f22,f37])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f37])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f37])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f49,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f36,plain,(
    k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_320,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k4_mcart_1(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0),sK2(X1,X2,X3,X4,X0),sK3(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_330,plain,
    ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2151,plain,
    ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK2(sK4,sK5,sK6,sK7,sK9),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_320,c_330])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_135,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_152,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_136,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_488,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_489,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_490,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_491,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_492,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_493,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_494,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_495,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_2356,plain,
    ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK2(sK4,sK5,sK6,sK7,sK9),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2151,c_13,c_12,c_11,c_10,c_152,c_489,c_491,c_493,c_495])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ m1_subset_1(X1,sK6)
    | ~ m1_subset_1(X2,sK5)
    | ~ m1_subset_1(X3,sK4)
    | k4_mcart_1(X3,X2,X1,X0) != sK9
    | sK8 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_321,plain,
    ( k4_mcart_1(X0,X1,X2,X3) != sK9
    | sK8 = X2
    | m1_subset_1(X3,sK7) != iProver_top
    | m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2359,plain,
    ( sK2(sK4,sK5,sK6,sK7,sK9) = sK8
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) != iProver_top
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2356,c_321])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_326,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK0(X2,X1,X0,X3,X4),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_867,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_326])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_327,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK1(X2,X1,X0,X3,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1023,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_327])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_328,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK2(X2,X1,X0,X3,X4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1172,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_328])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK3(X1,X2,X3,X4,X0),X4)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_329,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK3(X2,X1,X0,X3,X4),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1181,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_329])).

cnf(c_2432,plain,
    ( sK2(sK4,sK5,sK6,sK7,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2359,c_13,c_12,c_11,c_10,c_152,c_489,c_491,c_493,c_495,c_867,c_1023,c_1172,c_1181])).

cnf(c_2435,plain,
    ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK8,sK3(sK4,sK5,sK6,sK7,sK9)) = sK9 ),
    inference(demodulation,[status(thm)],[c_2432,c_2356])).

cnf(c_6,plain,
    ( ~ m1_subset_1(k4_mcart_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
    | k10_mcart_1(X4,X5,X6,X7,k4_mcart_1(X0,X1,X2,X3)) = X2
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_324,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3081,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK8,sK3(sK4,sK5,sK6,sK7,sK9))) = sK8
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_324])).

cnf(c_3104,plain,
    ( k10_mcart_1(X0,X1,X2,X3,sK9) = sK8
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3081,c_2435])).

cnf(c_3142,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_320,c_3104])).

cnf(c_9,negated_conjecture,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3142,c_495,c_493,c_491,c_489,c_152,c_9,c_10,c_11,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:33:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.73/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.02  
% 1.73/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.73/1.02  
% 1.73/1.02  ------  iProver source info
% 1.73/1.02  
% 1.73/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.73/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.73/1.02  git: non_committed_changes: false
% 1.73/1.02  git: last_make_outside_of_git: false
% 1.73/1.02  
% 1.73/1.02  ------ 
% 1.73/1.02  
% 1.73/1.02  ------ Input Options
% 1.73/1.02  
% 1.73/1.02  --out_options                           all
% 1.73/1.02  --tptp_safe_out                         true
% 1.73/1.02  --problem_path                          ""
% 1.73/1.02  --include_path                          ""
% 1.73/1.02  --clausifier                            res/vclausify_rel
% 1.73/1.02  --clausifier_options                    --mode clausify
% 1.73/1.02  --stdin                                 false
% 1.73/1.02  --stats_out                             all
% 1.73/1.02  
% 1.73/1.02  ------ General Options
% 1.73/1.02  
% 1.73/1.02  --fof                                   false
% 1.73/1.02  --time_out_real                         305.
% 1.73/1.02  --time_out_virtual                      -1.
% 1.73/1.02  --symbol_type_check                     false
% 1.73/1.02  --clausify_out                          false
% 1.73/1.02  --sig_cnt_out                           false
% 1.73/1.02  --trig_cnt_out                          false
% 1.73/1.02  --trig_cnt_out_tolerance                1.
% 1.73/1.02  --trig_cnt_out_sk_spl                   false
% 1.73/1.02  --abstr_cl_out                          false
% 1.73/1.02  
% 1.73/1.02  ------ Global Options
% 1.73/1.02  
% 1.73/1.02  --schedule                              default
% 1.73/1.02  --add_important_lit                     false
% 1.73/1.02  --prop_solver_per_cl                    1000
% 1.73/1.02  --min_unsat_core                        false
% 1.73/1.02  --soft_assumptions                      false
% 1.73/1.02  --soft_lemma_size                       3
% 1.73/1.02  --prop_impl_unit_size                   0
% 1.73/1.02  --prop_impl_unit                        []
% 1.73/1.02  --share_sel_clauses                     true
% 1.73/1.02  --reset_solvers                         false
% 1.73/1.02  --bc_imp_inh                            [conj_cone]
% 1.73/1.02  --conj_cone_tolerance                   3.
% 1.73/1.02  --extra_neg_conj                        none
% 1.73/1.02  --large_theory_mode                     true
% 1.73/1.02  --prolific_symb_bound                   200
% 1.73/1.02  --lt_threshold                          2000
% 1.73/1.02  --clause_weak_htbl                      true
% 1.73/1.02  --gc_record_bc_elim                     false
% 1.73/1.02  
% 1.73/1.02  ------ Preprocessing Options
% 1.73/1.02  
% 1.73/1.02  --preprocessing_flag                    true
% 1.73/1.02  --time_out_prep_mult                    0.1
% 1.73/1.02  --splitting_mode                        input
% 1.73/1.02  --splitting_grd                         true
% 1.73/1.02  --splitting_cvd                         false
% 1.73/1.02  --splitting_cvd_svl                     false
% 1.73/1.02  --splitting_nvd                         32
% 1.73/1.02  --sub_typing                            true
% 1.73/1.02  --prep_gs_sim                           true
% 1.73/1.02  --prep_unflatten                        true
% 1.73/1.02  --prep_res_sim                          true
% 1.73/1.02  --prep_upred                            true
% 1.73/1.02  --prep_sem_filter                       exhaustive
% 1.73/1.02  --prep_sem_filter_out                   false
% 1.73/1.02  --pred_elim                             true
% 1.73/1.02  --res_sim_input                         true
% 1.73/1.02  --eq_ax_congr_red                       true
% 1.73/1.02  --pure_diseq_elim                       true
% 1.73/1.02  --brand_transform                       false
% 1.73/1.02  --non_eq_to_eq                          false
% 1.73/1.02  --prep_def_merge                        true
% 1.73/1.02  --prep_def_merge_prop_impl              false
% 1.73/1.02  --prep_def_merge_mbd                    true
% 1.73/1.02  --prep_def_merge_tr_red                 false
% 1.73/1.02  --prep_def_merge_tr_cl                  false
% 1.73/1.02  --smt_preprocessing                     true
% 1.73/1.02  --smt_ac_axioms                         fast
% 1.73/1.02  --preprocessed_out                      false
% 1.73/1.02  --preprocessed_stats                    false
% 1.73/1.02  
% 1.73/1.02  ------ Abstraction refinement Options
% 1.73/1.02  
% 1.73/1.02  --abstr_ref                             []
% 1.73/1.02  --abstr_ref_prep                        false
% 1.73/1.02  --abstr_ref_until_sat                   false
% 1.73/1.02  --abstr_ref_sig_restrict                funpre
% 1.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/1.02  --abstr_ref_under                       []
% 1.73/1.02  
% 1.73/1.02  ------ SAT Options
% 1.73/1.02  
% 1.73/1.02  --sat_mode                              false
% 1.73/1.02  --sat_fm_restart_options                ""
% 1.73/1.02  --sat_gr_def                            false
% 1.73/1.02  --sat_epr_types                         true
% 1.73/1.02  --sat_non_cyclic_types                  false
% 1.73/1.02  --sat_finite_models                     false
% 1.73/1.02  --sat_fm_lemmas                         false
% 1.73/1.02  --sat_fm_prep                           false
% 1.73/1.02  --sat_fm_uc_incr                        true
% 1.73/1.02  --sat_out_model                         small
% 1.73/1.02  --sat_out_clauses                       false
% 1.73/1.02  
% 1.73/1.02  ------ QBF Options
% 1.73/1.02  
% 1.73/1.02  --qbf_mode                              false
% 1.73/1.02  --qbf_elim_univ                         false
% 1.73/1.02  --qbf_dom_inst                          none
% 1.73/1.02  --qbf_dom_pre_inst                      false
% 1.73/1.02  --qbf_sk_in                             false
% 1.73/1.02  --qbf_pred_elim                         true
% 1.73/1.02  --qbf_split                             512
% 1.73/1.02  
% 1.73/1.02  ------ BMC1 Options
% 1.73/1.02  
% 1.73/1.02  --bmc1_incremental                      false
% 1.73/1.02  --bmc1_axioms                           reachable_all
% 1.73/1.02  --bmc1_min_bound                        0
% 1.73/1.02  --bmc1_max_bound                        -1
% 1.73/1.02  --bmc1_max_bound_default                -1
% 1.73/1.02  --bmc1_symbol_reachability              true
% 1.73/1.02  --bmc1_property_lemmas                  false
% 1.73/1.02  --bmc1_k_induction                      false
% 1.73/1.02  --bmc1_non_equiv_states                 false
% 1.73/1.02  --bmc1_deadlock                         false
% 1.73/1.02  --bmc1_ucm                              false
% 1.73/1.02  --bmc1_add_unsat_core                   none
% 1.73/1.02  --bmc1_unsat_core_children              false
% 1.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.02  --bmc1_out_stat                         full
% 1.73/1.02  --bmc1_ground_init                      false
% 1.73/1.02  --bmc1_pre_inst_next_state              false
% 1.73/1.02  --bmc1_pre_inst_state                   false
% 1.73/1.02  --bmc1_pre_inst_reach_state             false
% 1.73/1.02  --bmc1_out_unsat_core                   false
% 1.73/1.02  --bmc1_aig_witness_out                  false
% 1.73/1.02  --bmc1_verbose                          false
% 1.73/1.02  --bmc1_dump_clauses_tptp                false
% 1.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.02  --bmc1_dump_file                        -
% 1.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.02  --bmc1_ucm_extend_mode                  1
% 1.73/1.02  --bmc1_ucm_init_mode                    2
% 1.73/1.02  --bmc1_ucm_cone_mode                    none
% 1.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.02  --bmc1_ucm_relax_model                  4
% 1.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.02  --bmc1_ucm_layered_model                none
% 1.73/1.02  --bmc1_ucm_max_lemma_size               10
% 1.73/1.02  
% 1.73/1.02  ------ AIG Options
% 1.73/1.02  
% 1.73/1.02  --aig_mode                              false
% 1.73/1.02  
% 1.73/1.02  ------ Instantiation Options
% 1.73/1.02  
% 1.73/1.02  --instantiation_flag                    true
% 1.73/1.02  --inst_sos_flag                         false
% 1.73/1.02  --inst_sos_phase                        true
% 1.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.02  --inst_lit_sel_side                     num_symb
% 1.73/1.02  --inst_solver_per_active                1400
% 1.73/1.02  --inst_solver_calls_frac                1.
% 1.73/1.02  --inst_passive_queue_type               priority_queues
% 1.73/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.02  --inst_passive_queues_freq              [25;2]
% 1.73/1.02  --inst_dismatching                      true
% 1.73/1.02  --inst_eager_unprocessed_to_passive     true
% 1.73/1.02  --inst_prop_sim_given                   true
% 1.73/1.02  --inst_prop_sim_new                     false
% 1.73/1.02  --inst_subs_new                         false
% 1.73/1.02  --inst_eq_res_simp                      false
% 1.73/1.02  --inst_subs_given                       false
% 1.73/1.02  --inst_orphan_elimination               true
% 1.73/1.02  --inst_learning_loop_flag               true
% 1.73/1.02  --inst_learning_start                   3000
% 1.73/1.02  --inst_learning_factor                  2
% 1.73/1.02  --inst_start_prop_sim_after_learn       3
% 1.73/1.02  --inst_sel_renew                        solver
% 1.73/1.02  --inst_lit_activity_flag                true
% 1.73/1.02  --inst_restr_to_given                   false
% 1.73/1.02  --inst_activity_threshold               500
% 1.73/1.02  --inst_out_proof                        true
% 1.73/1.02  
% 1.73/1.02  ------ Resolution Options
% 1.73/1.02  
% 1.73/1.02  --resolution_flag                       true
% 1.73/1.02  --res_lit_sel                           adaptive
% 1.73/1.02  --res_lit_sel_side                      none
% 1.73/1.02  --res_ordering                          kbo
% 1.73/1.02  --res_to_prop_solver                    active
% 1.73/1.02  --res_prop_simpl_new                    false
% 1.73/1.02  --res_prop_simpl_given                  true
% 1.73/1.02  --res_passive_queue_type                priority_queues
% 1.73/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.02  --res_passive_queues_freq               [15;5]
% 1.73/1.02  --res_forward_subs                      full
% 1.73/1.02  --res_backward_subs                     full
% 1.73/1.02  --res_forward_subs_resolution           true
% 1.73/1.02  --res_backward_subs_resolution          true
% 1.73/1.02  --res_orphan_elimination                true
% 1.73/1.02  --res_time_limit                        2.
% 1.73/1.02  --res_out_proof                         true
% 1.73/1.02  
% 1.73/1.02  ------ Superposition Options
% 1.73/1.02  
% 1.73/1.02  --superposition_flag                    true
% 1.73/1.02  --sup_passive_queue_type                priority_queues
% 1.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.02  --demod_completeness_check              fast
% 1.73/1.02  --demod_use_ground                      true
% 1.73/1.02  --sup_to_prop_solver                    passive
% 1.73/1.02  --sup_prop_simpl_new                    true
% 1.73/1.02  --sup_prop_simpl_given                  true
% 1.73/1.02  --sup_fun_splitting                     false
% 1.73/1.02  --sup_smt_interval                      50000
% 1.73/1.02  
% 1.73/1.02  ------ Superposition Simplification Setup
% 1.73/1.02  
% 1.73/1.02  --sup_indices_passive                   []
% 1.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.02  --sup_full_bw                           [BwDemod]
% 1.73/1.02  --sup_immed_triv                        [TrivRules]
% 1.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.02  --sup_immed_bw_main                     []
% 1.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.02  
% 1.73/1.02  ------ Combination Options
% 1.73/1.02  
% 1.73/1.02  --comb_res_mult                         3
% 1.73/1.02  --comb_sup_mult                         2
% 1.73/1.02  --comb_inst_mult                        10
% 1.73/1.02  
% 1.73/1.02  ------ Debug Options
% 1.73/1.02  
% 1.73/1.02  --dbg_backtrace                         false
% 1.73/1.02  --dbg_dump_prop_clauses                 false
% 1.73/1.02  --dbg_dump_prop_clauses_file            -
% 1.73/1.02  --dbg_out_stat                          false
% 1.73/1.02  ------ Parsing...
% 1.73/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.73/1.02  
% 1.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.73/1.02  
% 1.73/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.73/1.02  
% 1.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.73/1.02  ------ Proving...
% 1.73/1.02  ------ Problem Properties 
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  clauses                                 16
% 1.73/1.02  conjectures                             7
% 1.73/1.02  EPR                                     4
% 1.73/1.02  Horn                                    7
% 1.73/1.02  unary                                   6
% 1.73/1.02  binary                                  0
% 1.73/1.02  lits                                    66
% 1.73/1.02  lits eq                                 48
% 1.73/1.02  fd_pure                                 0
% 1.73/1.02  fd_pseudo                               0
% 1.73/1.02  fd_cond                                 5
% 1.73/1.02  fd_pseudo_cond                          0
% 1.73/1.02  AC symbols                              0
% 1.73/1.02  
% 1.73/1.02  ------ Schedule dynamic 5 is on 
% 1.73/1.02  
% 1.73/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  ------ 
% 1.73/1.02  Current options:
% 1.73/1.02  ------ 
% 1.73/1.02  
% 1.73/1.02  ------ Input Options
% 1.73/1.02  
% 1.73/1.02  --out_options                           all
% 1.73/1.02  --tptp_safe_out                         true
% 1.73/1.02  --problem_path                          ""
% 1.73/1.02  --include_path                          ""
% 1.73/1.02  --clausifier                            res/vclausify_rel
% 1.73/1.02  --clausifier_options                    --mode clausify
% 1.73/1.02  --stdin                                 false
% 1.73/1.02  --stats_out                             all
% 1.73/1.02  
% 1.73/1.02  ------ General Options
% 1.73/1.02  
% 1.73/1.02  --fof                                   false
% 1.73/1.02  --time_out_real                         305.
% 1.73/1.02  --time_out_virtual                      -1.
% 1.73/1.02  --symbol_type_check                     false
% 1.73/1.02  --clausify_out                          false
% 1.73/1.02  --sig_cnt_out                           false
% 1.73/1.02  --trig_cnt_out                          false
% 1.73/1.02  --trig_cnt_out_tolerance                1.
% 1.73/1.02  --trig_cnt_out_sk_spl                   false
% 1.73/1.02  --abstr_cl_out                          false
% 1.73/1.02  
% 1.73/1.02  ------ Global Options
% 1.73/1.02  
% 1.73/1.02  --schedule                              default
% 1.73/1.02  --add_important_lit                     false
% 1.73/1.02  --prop_solver_per_cl                    1000
% 1.73/1.02  --min_unsat_core                        false
% 1.73/1.02  --soft_assumptions                      false
% 1.73/1.02  --soft_lemma_size                       3
% 1.73/1.02  --prop_impl_unit_size                   0
% 1.73/1.02  --prop_impl_unit                        []
% 1.73/1.02  --share_sel_clauses                     true
% 1.73/1.02  --reset_solvers                         false
% 1.73/1.02  --bc_imp_inh                            [conj_cone]
% 1.73/1.02  --conj_cone_tolerance                   3.
% 1.73/1.02  --extra_neg_conj                        none
% 1.73/1.02  --large_theory_mode                     true
% 1.73/1.02  --prolific_symb_bound                   200
% 1.73/1.02  --lt_threshold                          2000
% 1.73/1.02  --clause_weak_htbl                      true
% 1.73/1.02  --gc_record_bc_elim                     false
% 1.73/1.02  
% 1.73/1.02  ------ Preprocessing Options
% 1.73/1.02  
% 1.73/1.02  --preprocessing_flag                    true
% 1.73/1.02  --time_out_prep_mult                    0.1
% 1.73/1.02  --splitting_mode                        input
% 1.73/1.02  --splitting_grd                         true
% 1.73/1.02  --splitting_cvd                         false
% 1.73/1.02  --splitting_cvd_svl                     false
% 1.73/1.02  --splitting_nvd                         32
% 1.73/1.02  --sub_typing                            true
% 1.73/1.02  --prep_gs_sim                           true
% 1.73/1.02  --prep_unflatten                        true
% 1.73/1.02  --prep_res_sim                          true
% 1.73/1.02  --prep_upred                            true
% 1.73/1.02  --prep_sem_filter                       exhaustive
% 1.73/1.02  --prep_sem_filter_out                   false
% 1.73/1.02  --pred_elim                             true
% 1.73/1.02  --res_sim_input                         true
% 1.73/1.02  --eq_ax_congr_red                       true
% 1.73/1.02  --pure_diseq_elim                       true
% 1.73/1.02  --brand_transform                       false
% 1.73/1.02  --non_eq_to_eq                          false
% 1.73/1.02  --prep_def_merge                        true
% 1.73/1.02  --prep_def_merge_prop_impl              false
% 1.73/1.02  --prep_def_merge_mbd                    true
% 1.73/1.02  --prep_def_merge_tr_red                 false
% 1.73/1.02  --prep_def_merge_tr_cl                  false
% 1.73/1.02  --smt_preprocessing                     true
% 1.73/1.02  --smt_ac_axioms                         fast
% 1.73/1.02  --preprocessed_out                      false
% 1.73/1.02  --preprocessed_stats                    false
% 1.73/1.02  
% 1.73/1.02  ------ Abstraction refinement Options
% 1.73/1.02  
% 1.73/1.02  --abstr_ref                             []
% 1.73/1.02  --abstr_ref_prep                        false
% 1.73/1.02  --abstr_ref_until_sat                   false
% 1.73/1.02  --abstr_ref_sig_restrict                funpre
% 1.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/1.02  --abstr_ref_under                       []
% 1.73/1.02  
% 1.73/1.02  ------ SAT Options
% 1.73/1.02  
% 1.73/1.02  --sat_mode                              false
% 1.73/1.02  --sat_fm_restart_options                ""
% 1.73/1.02  --sat_gr_def                            false
% 1.73/1.02  --sat_epr_types                         true
% 1.73/1.02  --sat_non_cyclic_types                  false
% 1.73/1.02  --sat_finite_models                     false
% 1.73/1.02  --sat_fm_lemmas                         false
% 1.73/1.02  --sat_fm_prep                           false
% 1.73/1.02  --sat_fm_uc_incr                        true
% 1.73/1.02  --sat_out_model                         small
% 1.73/1.02  --sat_out_clauses                       false
% 1.73/1.02  
% 1.73/1.02  ------ QBF Options
% 1.73/1.02  
% 1.73/1.02  --qbf_mode                              false
% 1.73/1.02  --qbf_elim_univ                         false
% 1.73/1.02  --qbf_dom_inst                          none
% 1.73/1.02  --qbf_dom_pre_inst                      false
% 1.73/1.02  --qbf_sk_in                             false
% 1.73/1.02  --qbf_pred_elim                         true
% 1.73/1.02  --qbf_split                             512
% 1.73/1.02  
% 1.73/1.02  ------ BMC1 Options
% 1.73/1.02  
% 1.73/1.02  --bmc1_incremental                      false
% 1.73/1.02  --bmc1_axioms                           reachable_all
% 1.73/1.02  --bmc1_min_bound                        0
% 1.73/1.02  --bmc1_max_bound                        -1
% 1.73/1.02  --bmc1_max_bound_default                -1
% 1.73/1.02  --bmc1_symbol_reachability              true
% 1.73/1.02  --bmc1_property_lemmas                  false
% 1.73/1.02  --bmc1_k_induction                      false
% 1.73/1.02  --bmc1_non_equiv_states                 false
% 1.73/1.02  --bmc1_deadlock                         false
% 1.73/1.02  --bmc1_ucm                              false
% 1.73/1.02  --bmc1_add_unsat_core                   none
% 1.73/1.02  --bmc1_unsat_core_children              false
% 1.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.02  --bmc1_out_stat                         full
% 1.73/1.02  --bmc1_ground_init                      false
% 1.73/1.02  --bmc1_pre_inst_next_state              false
% 1.73/1.02  --bmc1_pre_inst_state                   false
% 1.73/1.02  --bmc1_pre_inst_reach_state             false
% 1.73/1.02  --bmc1_out_unsat_core                   false
% 1.73/1.02  --bmc1_aig_witness_out                  false
% 1.73/1.02  --bmc1_verbose                          false
% 1.73/1.02  --bmc1_dump_clauses_tptp                false
% 1.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.02  --bmc1_dump_file                        -
% 1.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.02  --bmc1_ucm_extend_mode                  1
% 1.73/1.02  --bmc1_ucm_init_mode                    2
% 1.73/1.02  --bmc1_ucm_cone_mode                    none
% 1.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.02  --bmc1_ucm_relax_model                  4
% 1.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.02  --bmc1_ucm_layered_model                none
% 1.73/1.02  --bmc1_ucm_max_lemma_size               10
% 1.73/1.02  
% 1.73/1.02  ------ AIG Options
% 1.73/1.02  
% 1.73/1.02  --aig_mode                              false
% 1.73/1.02  
% 1.73/1.02  ------ Instantiation Options
% 1.73/1.02  
% 1.73/1.02  --instantiation_flag                    true
% 1.73/1.02  --inst_sos_flag                         false
% 1.73/1.02  --inst_sos_phase                        true
% 1.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.02  --inst_lit_sel_side                     none
% 1.73/1.02  --inst_solver_per_active                1400
% 1.73/1.02  --inst_solver_calls_frac                1.
% 1.73/1.02  --inst_passive_queue_type               priority_queues
% 1.73/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.02  --inst_passive_queues_freq              [25;2]
% 1.73/1.02  --inst_dismatching                      true
% 1.73/1.02  --inst_eager_unprocessed_to_passive     true
% 1.73/1.02  --inst_prop_sim_given                   true
% 1.73/1.02  --inst_prop_sim_new                     false
% 1.73/1.02  --inst_subs_new                         false
% 1.73/1.02  --inst_eq_res_simp                      false
% 1.73/1.02  --inst_subs_given                       false
% 1.73/1.02  --inst_orphan_elimination               true
% 1.73/1.02  --inst_learning_loop_flag               true
% 1.73/1.02  --inst_learning_start                   3000
% 1.73/1.02  --inst_learning_factor                  2
% 1.73/1.02  --inst_start_prop_sim_after_learn       3
% 1.73/1.02  --inst_sel_renew                        solver
% 1.73/1.02  --inst_lit_activity_flag                true
% 1.73/1.02  --inst_restr_to_given                   false
% 1.73/1.02  --inst_activity_threshold               500
% 1.73/1.02  --inst_out_proof                        true
% 1.73/1.02  
% 1.73/1.02  ------ Resolution Options
% 1.73/1.02  
% 1.73/1.02  --resolution_flag                       false
% 1.73/1.02  --res_lit_sel                           adaptive
% 1.73/1.02  --res_lit_sel_side                      none
% 1.73/1.02  --res_ordering                          kbo
% 1.73/1.02  --res_to_prop_solver                    active
% 1.73/1.02  --res_prop_simpl_new                    false
% 1.73/1.02  --res_prop_simpl_given                  true
% 1.73/1.02  --res_passive_queue_type                priority_queues
% 1.73/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.02  --res_passive_queues_freq               [15;5]
% 1.73/1.02  --res_forward_subs                      full
% 1.73/1.02  --res_backward_subs                     full
% 1.73/1.02  --res_forward_subs_resolution           true
% 1.73/1.02  --res_backward_subs_resolution          true
% 1.73/1.02  --res_orphan_elimination                true
% 1.73/1.02  --res_time_limit                        2.
% 1.73/1.02  --res_out_proof                         true
% 1.73/1.02  
% 1.73/1.02  ------ Superposition Options
% 1.73/1.02  
% 1.73/1.02  --superposition_flag                    true
% 1.73/1.02  --sup_passive_queue_type                priority_queues
% 1.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.02  --demod_completeness_check              fast
% 1.73/1.02  --demod_use_ground                      true
% 1.73/1.02  --sup_to_prop_solver                    passive
% 1.73/1.02  --sup_prop_simpl_new                    true
% 1.73/1.02  --sup_prop_simpl_given                  true
% 1.73/1.02  --sup_fun_splitting                     false
% 1.73/1.02  --sup_smt_interval                      50000
% 1.73/1.02  
% 1.73/1.02  ------ Superposition Simplification Setup
% 1.73/1.02  
% 1.73/1.02  --sup_indices_passive                   []
% 1.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.02  --sup_full_bw                           [BwDemod]
% 1.73/1.02  --sup_immed_triv                        [TrivRules]
% 1.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.02  --sup_immed_bw_main                     []
% 1.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.02  
% 1.73/1.02  ------ Combination Options
% 1.73/1.02  
% 1.73/1.02  --comb_res_mult                         3
% 1.73/1.02  --comb_sup_mult                         2
% 1.73/1.02  --comb_inst_mult                        10
% 1.73/1.02  
% 1.73/1.02  ------ Debug Options
% 1.73/1.02  
% 1.73/1.02  --dbg_backtrace                         false
% 1.73/1.02  --dbg_dump_prop_clauses                 false
% 1.73/1.02  --dbg_dump_prop_clauses_file            -
% 1.73/1.02  --dbg_out_stat                          false
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  ------ Proving...
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  % SZS status Theorem for theBenchmark.p
% 1.73/1.02  
% 1.73/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.73/1.02  
% 1.73/1.02  fof(f5,conjecture,(
% 1.73/1.02    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.02  
% 1.73/1.02  fof(f6,negated_conjecture,(
% 1.73/1.02    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.73/1.02    inference(negated_conjecture,[],[f5])).
% 1.73/1.02  
% 1.73/1.02  fof(f10,plain,(
% 1.73/1.02    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.73/1.02    inference(ennf_transformation,[],[f6])).
% 1.73/1.02  
% 1.73/1.02  fof(f11,plain,(
% 1.73/1.02    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.73/1.02    inference(flattening,[],[f10])).
% 1.73/1.02  
% 1.73/1.02  fof(f17,plain,(
% 1.73/1.02    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 1.73/1.02    introduced(choice_axiom,[])).
% 1.73/1.02  
% 1.73/1.02  fof(f18,plain,(
% 1.73/1.02    k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK8 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7)) | ~m1_subset_1(X8,sK6)) | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.73/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f11,f17])).
% 1.73/1.02  
% 1.73/1.02  fof(f30,plain,(
% 1.73/1.02    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.73/1.02    inference(cnf_transformation,[],[f18])).
% 1.73/1.02  
% 1.73/1.02  fof(f2,axiom,(
% 1.73/1.02    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 1.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.02  
% 1.73/1.02  fof(f20,plain,(
% 1.73/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.73/1.02    inference(cnf_transformation,[],[f2])).
% 1.73/1.02  
% 1.73/1.02  fof(f1,axiom,(
% 1.73/1.02    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.02  
% 1.73/1.02  fof(f19,plain,(
% 1.73/1.02    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.73/1.02    inference(cnf_transformation,[],[f1])).
% 1.73/1.02  
% 1.73/1.02  fof(f37,plain,(
% 1.73/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.73/1.02    inference(definition_unfolding,[],[f20,f19])).
% 1.73/1.02  
% 1.73/1.02  fof(f47,plain,(
% 1.73/1.02    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.73/1.02    inference(definition_unfolding,[],[f30,f37])).
% 1.73/1.02  
% 1.73/1.02  fof(f3,axiom,(
% 1.73/1.02    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.02  
% 1.73/1.02  fof(f7,plain,(
% 1.73/1.02    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.73/1.02    inference(ennf_transformation,[],[f3])).
% 1.73/1.02  
% 1.73/1.02  fof(f15,plain,(
% 1.73/1.02    ( ! [X6,X7,X5] : (! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(X5,X6,X7,sK3(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)))) )),
% 1.73/1.02    introduced(choice_axiom,[])).
% 1.73/1.02  
% 1.73/1.02  fof(f14,plain,(
% 1.73/1.02    ( ! [X6,X5] : (! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)))) )),
% 1.73/1.02    introduced(choice_axiom,[])).
% 1.73/1.02  
% 1.73/1.02  fof(f13,plain,(
% 1.73/1.02    ( ! [X5] : (! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)))) )),
% 1.73/1.02    introduced(choice_axiom,[])).
% 1.73/1.02  
% 1.73/1.02  fof(f12,plain,(
% 1.73/1.02    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)))),
% 1.73/1.02    introduced(choice_axiom,[])).
% 1.73/1.02  
% 1.73/1.02  fof(f16,plain,(
% 1.73/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.73/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).
% 1.73/1.02  
% 1.73/1.02  fof(f25,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(cnf_transformation,[],[f16])).
% 1.73/1.02  
% 1.73/1.02  fof(f38,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(definition_unfolding,[],[f25,f37])).
% 1.73/1.02  
% 1.73/1.02  fof(f32,plain,(
% 1.73/1.02    k1_xboole_0 != sK4),
% 1.73/1.02    inference(cnf_transformation,[],[f18])).
% 1.73/1.02  
% 1.73/1.02  fof(f33,plain,(
% 1.73/1.02    k1_xboole_0 != sK5),
% 1.73/1.02    inference(cnf_transformation,[],[f18])).
% 1.73/1.02  
% 1.73/1.02  fof(f34,plain,(
% 1.73/1.02    k1_xboole_0 != sK6),
% 1.73/1.02    inference(cnf_transformation,[],[f18])).
% 1.73/1.02  
% 1.73/1.02  fof(f35,plain,(
% 1.73/1.02    k1_xboole_0 != sK7),
% 1.73/1.02    inference(cnf_transformation,[],[f18])).
% 1.73/1.02  
% 1.73/1.02  fof(f31,plain,(
% 1.73/1.02    ( ! [X6,X8,X7,X9] : (sK8 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK9 | ~m1_subset_1(X9,sK7) | ~m1_subset_1(X8,sK6) | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4)) )),
% 1.73/1.02    inference(cnf_transformation,[],[f18])).
% 1.73/1.02  
% 1.73/1.02  fof(f21,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(cnf_transformation,[],[f16])).
% 1.73/1.02  
% 1.73/1.02  fof(f42,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(definition_unfolding,[],[f21,f37])).
% 1.73/1.02  
% 1.73/1.02  fof(f22,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(cnf_transformation,[],[f16])).
% 1.73/1.02  
% 1.73/1.02  fof(f41,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(definition_unfolding,[],[f22,f37])).
% 1.73/1.02  
% 1.73/1.02  fof(f23,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(cnf_transformation,[],[f16])).
% 1.73/1.02  
% 1.73/1.02  fof(f40,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(definition_unfolding,[],[f23,f37])).
% 1.73/1.02  
% 1.73/1.02  fof(f24,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(cnf_transformation,[],[f16])).
% 1.73/1.02  
% 1.73/1.02  fof(f39,plain,(
% 1.73/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/1.02    inference(definition_unfolding,[],[f24,f37])).
% 1.73/1.02  
% 1.73/1.02  fof(f4,axiom,(
% 1.73/1.02    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.02  
% 1.73/1.02  fof(f8,plain,(
% 1.73/1.02    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.73/1.02    inference(ennf_transformation,[],[f4])).
% 1.73/1.02  
% 1.73/1.02  fof(f9,plain,(
% 1.73/1.02    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.73/1.02    inference(flattening,[],[f8])).
% 1.73/1.02  
% 1.73/1.02  fof(f28,plain,(
% 1.73/1.02    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.73/1.02    inference(cnf_transformation,[],[f9])).
% 1.73/1.02  
% 1.73/1.02  fof(f44,plain,(
% 1.73/1.02    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 1.73/1.02    inference(definition_unfolding,[],[f28,f37])).
% 1.73/1.02  
% 1.73/1.02  fof(f49,plain,(
% 1.73/1.02    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 1.73/1.02    inference(equality_resolution,[],[f44])).
% 1.73/1.02  
% 1.73/1.02  fof(f36,plain,(
% 1.73/1.02    k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8),
% 1.73/1.02    inference(cnf_transformation,[],[f18])).
% 1.73/1.02  
% 1.73/1.02  cnf(c_15,negated_conjecture,
% 1.73/1.02      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 1.73/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_320,plain,
% 1.73/1.02      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_0,plain,
% 1.73/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 1.73/1.02      | k4_mcart_1(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0),sK2(X1,X2,X3,X4,X0),sK3(X1,X2,X3,X4,X0)) = X0
% 1.73/1.02      | k1_xboole_0 = X4
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1 ),
% 1.73/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_330,plain,
% 1.73/1.02      ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | k1_xboole_0 = X0
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_2151,plain,
% 1.73/1.02      ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK2(sK4,sK5,sK6,sK7,sK9),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9
% 1.73/1.02      | sK7 = k1_xboole_0
% 1.73/1.02      | sK6 = k1_xboole_0
% 1.73/1.02      | sK5 = k1_xboole_0
% 1.73/1.02      | sK4 = k1_xboole_0 ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_320,c_330]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_13,negated_conjecture,
% 1.73/1.02      ( k1_xboole_0 != sK4 ),
% 1.73/1.02      inference(cnf_transformation,[],[f32]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_12,negated_conjecture,
% 1.73/1.02      ( k1_xboole_0 != sK5 ),
% 1.73/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_11,negated_conjecture,
% 1.73/1.02      ( k1_xboole_0 != sK6 ),
% 1.73/1.02      inference(cnf_transformation,[],[f34]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_10,negated_conjecture,
% 1.73/1.02      ( k1_xboole_0 != sK7 ),
% 1.73/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_135,plain,( X0 = X0 ),theory(equality) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_152,plain,
% 1.73/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_135]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_136,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_488,plain,
% 1.73/1.02      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_136]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_489,plain,
% 1.73/1.02      ( sK7 != k1_xboole_0
% 1.73/1.02      | k1_xboole_0 = sK7
% 1.73/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_488]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_490,plain,
% 1.73/1.02      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_136]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_491,plain,
% 1.73/1.02      ( sK6 != k1_xboole_0
% 1.73/1.02      | k1_xboole_0 = sK6
% 1.73/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_490]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_492,plain,
% 1.73/1.02      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_136]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_493,plain,
% 1.73/1.02      ( sK5 != k1_xboole_0
% 1.73/1.02      | k1_xboole_0 = sK5
% 1.73/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_492]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_494,plain,
% 1.73/1.02      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_136]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_495,plain,
% 1.73/1.02      ( sK4 != k1_xboole_0
% 1.73/1.02      | k1_xboole_0 = sK4
% 1.73/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.73/1.02      inference(instantiation,[status(thm)],[c_494]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_2356,plain,
% 1.73/1.02      ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK2(sK4,sK5,sK6,sK7,sK9),sK3(sK4,sK5,sK6,sK7,sK9)) = sK9 ),
% 1.73/1.02      inference(global_propositional_subsumption,
% 1.73/1.02                [status(thm)],
% 1.73/1.02                [c_2151,c_13,c_12,c_11,c_10,c_152,c_489,c_491,c_493,
% 1.73/1.02                 c_495]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_14,negated_conjecture,
% 1.73/1.02      ( ~ m1_subset_1(X0,sK7)
% 1.73/1.02      | ~ m1_subset_1(X1,sK6)
% 1.73/1.02      | ~ m1_subset_1(X2,sK5)
% 1.73/1.02      | ~ m1_subset_1(X3,sK4)
% 1.73/1.02      | k4_mcart_1(X3,X2,X1,X0) != sK9
% 1.73/1.02      | sK8 = X1 ),
% 1.73/1.02      inference(cnf_transformation,[],[f31]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_321,plain,
% 1.73/1.02      ( k4_mcart_1(X0,X1,X2,X3) != sK9
% 1.73/1.02      | sK8 = X2
% 1.73/1.02      | m1_subset_1(X3,sK7) != iProver_top
% 1.73/1.02      | m1_subset_1(X2,sK6) != iProver_top
% 1.73/1.02      | m1_subset_1(X1,sK5) != iProver_top
% 1.73/1.02      | m1_subset_1(X0,sK4) != iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_2359,plain,
% 1.73/1.02      ( sK2(sK4,sK5,sK6,sK7,sK9) = sK8
% 1.73/1.02      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) != iProver_top
% 1.73/1.02      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) != iProver_top
% 1.73/1.02      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) != iProver_top
% 1.73/1.02      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) != iProver_top ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_2356,c_321]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_4,plain,
% 1.73/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 1.73/1.02      | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
% 1.73/1.02      | k1_xboole_0 = X4
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1 ),
% 1.73/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_326,plain,
% 1.73/1.02      ( k1_xboole_0 = X0
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 1.73/1.02      | m1_subset_1(sK0(X2,X1,X0,X3,X4),X2) = iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_867,plain,
% 1.73/1.02      ( sK7 = k1_xboole_0
% 1.73/1.02      | sK6 = k1_xboole_0
% 1.73/1.02      | sK5 = k1_xboole_0
% 1.73/1.02      | sK4 = k1_xboole_0
% 1.73/1.02      | m1_subset_1(sK0(sK4,sK5,sK6,sK7,sK9),sK4) = iProver_top ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_320,c_326]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_3,plain,
% 1.73/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 1.73/1.02      | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
% 1.73/1.02      | k1_xboole_0 = X4
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1 ),
% 1.73/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_327,plain,
% 1.73/1.02      ( k1_xboole_0 = X0
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 1.73/1.02      | m1_subset_1(sK1(X2,X1,X0,X3,X4),X1) = iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_1023,plain,
% 1.73/1.02      ( sK7 = k1_xboole_0
% 1.73/1.02      | sK6 = k1_xboole_0
% 1.73/1.02      | sK5 = k1_xboole_0
% 1.73/1.02      | sK4 = k1_xboole_0
% 1.73/1.02      | m1_subset_1(sK1(sK4,sK5,sK6,sK7,sK9),sK5) = iProver_top ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_320,c_327]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_2,plain,
% 1.73/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 1.73/1.02      | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
% 1.73/1.02      | k1_xboole_0 = X4
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1 ),
% 1.73/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_328,plain,
% 1.73/1.02      ( k1_xboole_0 = X0
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 1.73/1.02      | m1_subset_1(sK2(X2,X1,X0,X3,X4),X0) = iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_1172,plain,
% 1.73/1.02      ( sK7 = k1_xboole_0
% 1.73/1.02      | sK6 = k1_xboole_0
% 1.73/1.02      | sK5 = k1_xboole_0
% 1.73/1.02      | sK4 = k1_xboole_0
% 1.73/1.02      | m1_subset_1(sK2(sK4,sK5,sK6,sK7,sK9),sK6) = iProver_top ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_320,c_328]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_1,plain,
% 1.73/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 1.73/1.02      | m1_subset_1(sK3(X1,X2,X3,X4,X0),X4)
% 1.73/1.02      | k1_xboole_0 = X4
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1 ),
% 1.73/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_329,plain,
% 1.73/1.02      ( k1_xboole_0 = X0
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 1.73/1.02      | m1_subset_1(sK3(X2,X1,X0,X3,X4),X3) = iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_1181,plain,
% 1.73/1.02      ( sK7 = k1_xboole_0
% 1.73/1.02      | sK6 = k1_xboole_0
% 1.73/1.02      | sK5 = k1_xboole_0
% 1.73/1.02      | sK4 = k1_xboole_0
% 1.73/1.02      | m1_subset_1(sK3(sK4,sK5,sK6,sK7,sK9),sK7) = iProver_top ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_320,c_329]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_2432,plain,
% 1.73/1.02      ( sK2(sK4,sK5,sK6,sK7,sK9) = sK8 ),
% 1.73/1.02      inference(global_propositional_subsumption,
% 1.73/1.02                [status(thm)],
% 1.73/1.02                [c_2359,c_13,c_12,c_11,c_10,c_152,c_489,c_491,c_493,
% 1.73/1.02                 c_495,c_867,c_1023,c_1172,c_1181]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_2435,plain,
% 1.73/1.02      ( k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK8,sK3(sK4,sK5,sK6,sK7,sK9)) = sK9 ),
% 1.73/1.02      inference(demodulation,[status(thm)],[c_2432,c_2356]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_6,plain,
% 1.73/1.02      ( ~ m1_subset_1(k4_mcart_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
% 1.73/1.02      | k10_mcart_1(X4,X5,X6,X7,k4_mcart_1(X0,X1,X2,X3)) = X2
% 1.73/1.02      | k1_xboole_0 = X7
% 1.73/1.02      | k1_xboole_0 = X6
% 1.73/1.02      | k1_xboole_0 = X5
% 1.73/1.02      | k1_xboole_0 = X4 ),
% 1.73/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_324,plain,
% 1.73/1.02      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
% 1.73/1.02      | k1_xboole_0 = X0
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 1.73/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_3081,plain,
% 1.73/1.02      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK0(sK4,sK5,sK6,sK7,sK9),sK1(sK4,sK5,sK6,sK7,sK9),sK8,sK3(sK4,sK5,sK6,sK7,sK9))) = sK8
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | k1_xboole_0 = X0
% 1.73/1.02      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_2435,c_324]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_3104,plain,
% 1.73/1.02      ( k10_mcart_1(X0,X1,X2,X3,sK9) = sK8
% 1.73/1.02      | k1_xboole_0 = X3
% 1.73/1.02      | k1_xboole_0 = X2
% 1.73/1.02      | k1_xboole_0 = X1
% 1.73/1.02      | k1_xboole_0 = X0
% 1.73/1.02      | m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 1.73/1.02      inference(light_normalisation,[status(thm)],[c_3081,c_2435]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_3142,plain,
% 1.73/1.02      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) = sK8
% 1.73/1.02      | sK7 = k1_xboole_0
% 1.73/1.02      | sK6 = k1_xboole_0
% 1.73/1.02      | sK5 = k1_xboole_0
% 1.73/1.02      | sK4 = k1_xboole_0 ),
% 1.73/1.02      inference(superposition,[status(thm)],[c_320,c_3104]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(c_9,negated_conjecture,
% 1.73/1.02      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK9) != sK8 ),
% 1.73/1.02      inference(cnf_transformation,[],[f36]) ).
% 1.73/1.02  
% 1.73/1.02  cnf(contradiction,plain,
% 1.73/1.02      ( $false ),
% 1.73/1.02      inference(minisat,
% 1.73/1.02                [status(thm)],
% 1.73/1.02                [c_3142,c_495,c_493,c_491,c_489,c_152,c_9,c_10,c_11,c_12,
% 1.73/1.02                 c_13]) ).
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/1.02  
% 1.73/1.02  ------                               Statistics
% 1.73/1.02  
% 1.73/1.02  ------ General
% 1.73/1.02  
% 1.73/1.02  abstr_ref_over_cycles:                  0
% 1.73/1.02  abstr_ref_under_cycles:                 0
% 1.73/1.02  gc_basic_clause_elim:                   0
% 1.73/1.02  forced_gc_time:                         0
% 1.73/1.02  parsing_time:                           0.009
% 1.73/1.02  unif_index_cands_time:                  0.
% 1.73/1.02  unif_index_add_time:                    0.
% 1.73/1.02  orderings_time:                         0.
% 1.73/1.02  out_proof_time:                         0.01
% 1.73/1.02  total_time:                             0.187
% 1.73/1.02  num_of_symbols:                         49
% 1.73/1.02  num_of_terms:                           9228
% 1.73/1.02  
% 1.73/1.02  ------ Preprocessing
% 1.73/1.02  
% 1.73/1.02  num_of_splits:                          0
% 1.73/1.02  num_of_split_atoms:                     0
% 1.73/1.02  num_of_reused_defs:                     0
% 1.73/1.02  num_eq_ax_congr_red:                    64
% 1.73/1.02  num_of_sem_filtered_clauses:            1
% 1.73/1.02  num_of_subtypes:                        0
% 1.73/1.02  monotx_restored_types:                  0
% 1.73/1.02  sat_num_of_epr_types:                   0
% 1.73/1.02  sat_num_of_non_cyclic_types:            0
% 1.73/1.02  sat_guarded_non_collapsed_types:        0
% 1.73/1.02  num_pure_diseq_elim:                    0
% 1.73/1.02  simp_replaced_by:                       0
% 1.73/1.02  res_preprocessed:                       67
% 1.73/1.02  prep_upred:                             0
% 1.73/1.02  prep_unflattend:                        0
% 1.73/1.02  smt_new_axioms:                         0
% 1.73/1.02  pred_elim_cands:                        1
% 1.73/1.02  pred_elim:                              0
% 1.73/1.02  pred_elim_cl:                           0
% 1.73/1.02  pred_elim_cycles:                       1
% 1.73/1.02  merged_defs:                            0
% 1.73/1.02  merged_defs_ncl:                        0
% 1.73/1.02  bin_hyper_res:                          0
% 1.73/1.02  prep_cycles:                            3
% 1.73/1.02  pred_elim_time:                         0.
% 1.73/1.02  splitting_time:                         0.
% 1.73/1.02  sem_filter_time:                        0.
% 1.73/1.02  monotx_time:                            0.
% 1.73/1.02  subtype_inf_time:                       0.
% 1.73/1.02  
% 1.73/1.02  ------ Problem properties
% 1.73/1.02  
% 1.73/1.02  clauses:                                16
% 1.73/1.02  conjectures:                            7
% 1.73/1.02  epr:                                    4
% 1.73/1.02  horn:                                   7
% 1.73/1.02  ground:                                 6
% 1.73/1.02  unary:                                  6
% 1.73/1.02  binary:                                 0
% 1.73/1.02  lits:                                   66
% 1.73/1.02  lits_eq:                                48
% 1.73/1.02  fd_pure:                                0
% 1.73/1.02  fd_pseudo:                              0
% 1.73/1.02  fd_cond:                                5
% 1.73/1.02  fd_pseudo_cond:                         0
% 1.73/1.02  ac_symbols:                             0
% 1.73/1.02  
% 1.73/1.02  ------ Propositional Solver
% 1.73/1.02  
% 1.73/1.02  prop_solver_calls:                      22
% 1.73/1.02  prop_fast_solver_calls:                 662
% 1.73/1.02  smt_solver_calls:                       0
% 1.73/1.02  smt_fast_solver_calls:                  0
% 1.73/1.02  prop_num_of_clauses:                    1422
% 1.73/1.02  prop_preprocess_simplified:             5390
% 1.73/1.02  prop_fo_subsumed:                       36
% 1.73/1.02  prop_solver_time:                       0.
% 1.73/1.02  smt_solver_time:                        0.
% 1.73/1.02  smt_fast_solver_time:                   0.
% 1.73/1.02  prop_fast_solver_time:                  0.
% 1.73/1.02  prop_unsat_core_time:                   0.
% 1.73/1.02  
% 1.73/1.02  ------ QBF
% 1.73/1.02  
% 1.73/1.02  qbf_q_res:                              0
% 1.73/1.02  qbf_num_tautologies:                    0
% 1.73/1.02  qbf_prep_cycles:                        0
% 1.73/1.02  
% 1.73/1.02  ------ BMC1
% 1.73/1.02  
% 1.73/1.02  bmc1_current_bound:                     -1
% 1.73/1.02  bmc1_last_solved_bound:                 -1
% 1.73/1.02  bmc1_unsat_core_size:                   -1
% 1.73/1.02  bmc1_unsat_core_parents_size:           -1
% 1.73/1.02  bmc1_merge_next_fun:                    0
% 1.73/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.73/1.02  
% 1.73/1.02  ------ Instantiation
% 1.73/1.02  
% 1.73/1.02  inst_num_of_clauses:                    469
% 1.73/1.02  inst_num_in_passive:                    300
% 1.73/1.02  inst_num_in_active:                     160
% 1.73/1.02  inst_num_in_unprocessed:                9
% 1.73/1.02  inst_num_of_loops:                      160
% 1.73/1.02  inst_num_of_learning_restarts:          0
% 1.73/1.02  inst_num_moves_active_passive:          0
% 1.73/1.02  inst_lit_activity:                      0
% 1.73/1.02  inst_lit_activity_moves:                0
% 1.73/1.02  inst_num_tautologies:                   0
% 1.73/1.02  inst_num_prop_implied:                  0
% 1.73/1.02  inst_num_existing_simplified:           0
% 1.73/1.02  inst_num_eq_res_simplified:             0
% 1.73/1.02  inst_num_child_elim:                    0
% 1.73/1.02  inst_num_of_dismatching_blockings:      0
% 1.73/1.02  inst_num_of_non_proper_insts:           437
% 1.73/1.02  inst_num_of_duplicates:                 0
% 1.73/1.02  inst_inst_num_from_inst_to_res:         0
% 1.73/1.02  inst_dismatching_checking_time:         0.
% 1.73/1.02  
% 1.73/1.02  ------ Resolution
% 1.73/1.02  
% 1.73/1.02  res_num_of_clauses:                     0
% 1.73/1.02  res_num_in_passive:                     0
% 1.73/1.02  res_num_in_active:                      0
% 1.73/1.02  res_num_of_loops:                       70
% 1.73/1.02  res_forward_subset_subsumed:            5
% 1.73/1.02  res_backward_subset_subsumed:           0
% 1.73/1.02  res_forward_subsumed:                   0
% 1.73/1.02  res_backward_subsumed:                  0
% 1.73/1.02  res_forward_subsumption_resolution:     0
% 1.73/1.02  res_backward_subsumption_resolution:    0
% 1.73/1.02  res_clause_to_clause_subsumption:       24
% 1.73/1.02  res_orphan_elimination:                 0
% 1.73/1.02  res_tautology_del:                      0
% 1.73/1.02  res_num_eq_res_simplified:              0
% 1.73/1.02  res_num_sel_changes:                    0
% 1.73/1.02  res_moves_from_active_to_pass:          0
% 1.73/1.02  
% 1.73/1.02  ------ Superposition
% 1.73/1.02  
% 1.73/1.02  sup_time_total:                         0.
% 1.73/1.02  sup_time_generating:                    0.
% 1.73/1.02  sup_time_sim_full:                      0.
% 1.73/1.02  sup_time_sim_immed:                     0.
% 1.73/1.02  
% 1.73/1.02  sup_num_of_clauses:                     31
% 1.73/1.02  sup_num_in_active:                      29
% 1.73/1.02  sup_num_in_passive:                     2
% 1.73/1.02  sup_num_of_loops:                       30
% 1.73/1.02  sup_fw_superposition:                   9
% 1.73/1.02  sup_bw_superposition:                   10
% 1.73/1.02  sup_immediate_simplified:               8
% 1.73/1.02  sup_given_eliminated:                   0
% 1.73/1.02  comparisons_done:                       0
% 1.73/1.02  comparisons_avoided:                    16
% 1.73/1.02  
% 1.73/1.02  ------ Simplifications
% 1.73/1.02  
% 1.73/1.02  
% 1.73/1.02  sim_fw_subset_subsumed:                 0
% 1.73/1.02  sim_bw_subset_subsumed:                 0
% 1.73/1.02  sim_fw_subsumed:                        0
% 1.73/1.02  sim_bw_subsumed:                        0
% 1.73/1.02  sim_fw_subsumption_res:                 0
% 1.73/1.02  sim_bw_subsumption_res:                 0
% 1.73/1.02  sim_tautology_del:                      0
% 1.73/1.02  sim_eq_tautology_del:                   1
% 1.73/1.02  sim_eq_res_simp:                        0
% 1.73/1.02  sim_fw_demodulated:                     0
% 1.73/1.02  sim_bw_demodulated:                     2
% 1.73/1.02  sim_light_normalised:                   9
% 1.73/1.02  sim_joinable_taut:                      0
% 1.73/1.02  sim_joinable_simp:                      0
% 1.73/1.02  sim_ac_normalised:                      0
% 1.73/1.02  sim_smt_subsumption:                    0
% 1.73/1.02  
%------------------------------------------------------------------------------
