%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:59 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 746 expanded)
%              Number of clauses        :   52 ( 259 expanded)
%              Number of leaves         :   11 ( 204 expanded)
%              Depth                    :   22
%              Number of atoms          :  388 (5179 expanded)
%              Number of equality atoms :  290 (3287 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X6
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X6
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f14,f19])).

fof(f33,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X4,X5,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(X4,X5,X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(X4,X5,sK2(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK2(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(X4,X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(X4,sK1(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK1(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK0(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK2(X0,X1,X2,X3),X2)
            & m1_subset_1(sK1(X0,X1,X2,X3),X1)
            & m1_subset_1(sK0(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),sK2(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f35,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X6
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X6
      | k4_tarski(k4_tarski(X5,X6),X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f34,f21])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f31,f21])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_375,plain,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(sK0(X1,X2,X3,X0),X1)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_383,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
    | m1_subset_1(sK0(X1,X0,X2,X3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(sK1(X1,X2,X3,X0),X2)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_384,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
    | m1_subset_1(sK1(X1,X0,X2,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k4_tarski(k4_tarski(sK0(X1,X2,X3,X0),sK1(X1,X2,X3,X0)),sK2(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_386,plain,
    ( k4_tarski(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),sK2(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2038,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK1(sK3,sK4,sK5,sK7)),sK2(sK3,sK4,sK5,sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_375,c_386])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_158,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_177,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_159,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_541,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_542,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_543,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_544,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_545,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_546,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_2112,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK1(sK3,sK4,sK5,sK7)),sK2(sK3,sK4,sK5,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2038,c_14,c_13,c_12,c_177,c_542,c_544,c_546])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(X1,sK4)
    | ~ m1_subset_1(X2,sK3)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK7
    | sK6 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_376,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
    | sK6 = X1
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2116,plain,
    ( sK1(sK3,sK4,sK5,sK7) = sK6
    | m1_subset_1(sK2(sK3,sK4,sK5,sK7),sK5) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_376])).

cnf(c_17,plain,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(sK2(X1,X2,X3,X0),X3)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,sK5))
    | m1_subset_1(sK2(X1,X2,sK5,X0),sK5)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK4,sK5))
    | m1_subset_1(sK2(X1,sK4,sK5,X0),sK5)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(sK3,sK4,sK5))
    | m1_subset_1(sK2(sK3,sK4,sK5,X0),sK5)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1934,plain,
    ( m1_subset_1(sK2(sK3,sK4,sK5,sK7),sK5)
    | ~ m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_1935,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | m1_subset_1(sK2(sK3,sK4,sK5,sK7),sK5) = iProver_top
    | m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_2218,plain,
    ( sK1(sK3,sK4,sK5,sK7) = sK6
    | m1_subset_1(sK1(sK3,sK4,sK5,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2116,c_17,c_14,c_13,c_12,c_1935])).

cnf(c_2225,plain,
    ( sK1(sK3,sK4,sK5,sK7) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_384,c_2218])).

cnf(c_2231,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top
    | sK1(sK3,sK4,sK5,sK7) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2225,c_17,c_14,c_13,c_12,c_177,c_542,c_544,c_546])).

cnf(c_2232,plain,
    ( sK1(sK3,sK4,sK5,sK7) = sK6
    | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2231])).

cnf(c_2237,plain,
    ( sK1(sK3,sK4,sK5,sK7) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_383,c_2232])).

cnf(c_2240,plain,
    ( sK1(sK3,sK4,sK5,sK7) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2237,c_17,c_14,c_13,c_12,c_177,c_542,c_544,c_546])).

cnf(c_2243,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK6),sK2(sK3,sK4,sK5,sK7)) = sK7 ),
    inference(demodulation,[status(thm)],[c_2240,c_2112])).

cnf(c_9,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k3_zfmisc_1(X3,X4,X5))
    | k6_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X1
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_378,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2285,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK6),sK2(sK3,sK4,sK5,sK7))) = sK6
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2243,c_378])).

cnf(c_2298,plain,
    ( k6_mcart_1(X0,X1,X2,sK7) = sK6
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2285,c_2243])).

cnf(c_3037,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_375,c_2298])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_381,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1208,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_375,c_381])).

cnf(c_1690,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1208,c_14,c_13,c_12,c_177,c_542,c_544,c_546])).

cnf(c_3038,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3037,c_1690])).

cnf(c_11,negated_conjecture,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1693,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) != sK6 ),
    inference(demodulation,[status(thm)],[c_1690,c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3038,c_1693,c_546,c_544,c_542,c_177,c_12,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.93/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/0.99  
% 1.93/0.99  ------  iProver source info
% 1.93/0.99  
% 1.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/0.99  git: non_committed_changes: false
% 1.93/0.99  git: last_make_outside_of_git: false
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     num_symb
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       true
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  ------ Parsing...
% 1.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/0.99  ------ Proving...
% 1.93/0.99  ------ Problem Properties 
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  clauses                                 17
% 1.93/0.99  conjectures                             6
% 1.93/0.99  EPR                                     3
% 1.93/0.99  Horn                                    7
% 1.93/0.99  unary                                   5
% 1.93/0.99  binary                                  1
% 1.93/0.99  lits                                    62
% 1.93/0.99  lits eq                                 43
% 1.93/0.99  fd_pure                                 0
% 1.93/0.99  fd_pseudo                               0
% 1.93/0.99  fd_cond                                 7
% 1.93/0.99  fd_pseudo_cond                          0
% 1.93/0.99  AC symbols                              0
% 1.93/0.99  
% 1.93/0.99  ------ Schedule dynamic 5 is on 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  Current options:
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     none
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       false
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ Proving...
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS status Theorem for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  fof(f6,conjecture,(
% 1.93/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f7,negated_conjecture,(
% 1.93/0.99    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.93/0.99    inference(negated_conjecture,[],[f6])).
% 1.93/0.99  
% 1.93/0.99  fof(f13,plain,(
% 1.93/0.99    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.93/0.99    inference(ennf_transformation,[],[f7])).
% 1.93/0.99  
% 1.93/0.99  fof(f14,plain,(
% 1.93/0.99    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.93/0.99    inference(flattening,[],[f13])).
% 1.93/0.99  
% 1.93/0.99  fof(f19,plain,(
% 1.93/0.99    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f20,plain,(
% 1.93/0.99    k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f14,f19])).
% 1.93/0.99  
% 1.93/0.99  fof(f33,plain,(
% 1.93/0.99    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.93/0.99    inference(cnf_transformation,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  fof(f3,axiom,(
% 1.93/0.99    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f9,plain,(
% 1.93/0.99    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.93/0.99    inference(ennf_transformation,[],[f3])).
% 1.93/0.99  
% 1.93/0.99  fof(f17,plain,(
% 1.93/0.99    ( ! [X4,X5] : (! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(X4,X5,sK2(X0,X1,X2,X3)) = X3 & m1_subset_1(sK2(X0,X1,X2,X3),X2)))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f16,plain,(
% 1.93/0.99    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(X4,sK1(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f15,plain,(
% 1.93/0.99    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK0(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0)))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f18,plain,(
% 1.93/0.99    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)) = X3 & m1_subset_1(sK2(X0,X1,X2,X3),X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).
% 1.93/0.99  
% 1.93/0.99  fof(f23,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK0(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.93/0.99    inference(cnf_transformation,[],[f18])).
% 1.93/0.99  
% 1.93/0.99  fof(f24,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.93/0.99    inference(cnf_transformation,[],[f18])).
% 1.93/0.99  
% 1.93/0.99  fof(f26,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.93/0.99    inference(cnf_transformation,[],[f18])).
% 1.93/0.99  
% 1.93/0.99  fof(f1,axiom,(
% 1.93/0.99    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f21,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f1])).
% 1.93/0.99  
% 1.93/0.99  fof(f39,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),sK2(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.93/0.99    inference(definition_unfolding,[],[f26,f21])).
% 1.93/0.99  
% 1.93/0.99  fof(f35,plain,(
% 1.93/0.99    k1_xboole_0 != sK3),
% 1.93/0.99    inference(cnf_transformation,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  fof(f36,plain,(
% 1.93/0.99    k1_xboole_0 != sK4),
% 1.93/0.99    inference(cnf_transformation,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  fof(f37,plain,(
% 1.93/0.99    k1_xboole_0 != sK5),
% 1.93/0.99    inference(cnf_transformation,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  fof(f34,plain,(
% 1.93/0.99    ( ! [X6,X7,X5] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  fof(f43,plain,(
% 1.93/0.99    ( ! [X6,X7,X5] : (sK6 = X6 | k4_tarski(k4_tarski(X5,X6),X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 1.93/0.99    inference(definition_unfolding,[],[f34,f21])).
% 1.93/0.99  
% 1.93/0.99  fof(f25,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.93/0.99    inference(cnf_transformation,[],[f18])).
% 1.93/0.99  
% 1.93/0.99  fof(f5,axiom,(
% 1.93/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f11,plain,(
% 1.93/0.99    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.93/0.99    inference(ennf_transformation,[],[f5])).
% 1.93/0.99  
% 1.93/0.99  fof(f12,plain,(
% 1.93/0.99    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.93/0.99    inference(flattening,[],[f11])).
% 1.93/0.99  
% 1.93/0.99  fof(f31,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.93/0.99    inference(cnf_transformation,[],[f12])).
% 1.93/0.99  
% 1.93/0.99  fof(f41,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.93/0.99    inference(definition_unfolding,[],[f31,f21])).
% 1.93/0.99  
% 1.93/0.99  fof(f45,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X5,X1] : (k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2))) )),
% 1.93/0.99    inference(equality_resolution,[],[f41])).
% 1.93/0.99  
% 1.93/0.99  fof(f4,axiom,(
% 1.93/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f10,plain,(
% 1.93/0.99    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.93/0.99    inference(ennf_transformation,[],[f4])).
% 1.93/0.99  
% 1.93/0.99  fof(f28,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.93/0.99    inference(cnf_transformation,[],[f10])).
% 1.93/0.99  
% 1.93/0.99  fof(f38,plain,(
% 1.93/0.99    k6_mcart_1(sK3,sK4,sK5,sK7) != sK6),
% 1.93/0.99    inference(cnf_transformation,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  cnf(c_16,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_375,plain,
% 1.93/0.99      ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 1.93/0.99      | m1_subset_1(sK0(X1,X2,X3,X0),X1)
% 1.93/0.99      | k1_xboole_0 = X3
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1 ),
% 1.93/0.99      inference(cnf_transformation,[],[f23]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_383,plain,
% 1.93/0.99      ( k1_xboole_0 = X0
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK0(X1,X0,X2,X3),X1) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 1.93/0.99      | m1_subset_1(sK1(X1,X2,X3,X0),X2)
% 1.93/0.99      | k1_xboole_0 = X3
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1 ),
% 1.93/0.99      inference(cnf_transformation,[],[f24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_384,plain,
% 1.93/0.99      ( k1_xboole_0 = X0
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK1(X1,X0,X2,X3),X0) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 1.93/0.99      | k4_tarski(k4_tarski(sK0(X1,X2,X3,X0),sK1(X1,X2,X3,X0)),sK2(X1,X2,X3,X0)) = X0
% 1.93/0.99      | k1_xboole_0 = X3
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1 ),
% 1.93/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_386,plain,
% 1.93/0.99      ( k4_tarski(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),sK2(X0,X1,X2,X3)) = X3
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = X0
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2038,plain,
% 1.93/0.99      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK1(sK3,sK4,sK5,sK7)),sK2(sK3,sK4,sK5,sK7)) = sK7
% 1.93/0.99      | sK5 = k1_xboole_0
% 1.93/0.99      | sK4 = k1_xboole_0
% 1.93/0.99      | sK3 = k1_xboole_0 ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_375,c_386]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_14,negated_conjecture,
% 1.93/0.99      ( k1_xboole_0 != sK3 ),
% 1.93/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_13,negated_conjecture,
% 1.93/0.99      ( k1_xboole_0 != sK4 ),
% 1.93/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_12,negated_conjecture,
% 1.93/0.99      ( k1_xboole_0 != sK5 ),
% 1.93/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_158,plain,( X0 = X0 ),theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_177,plain,
% 1.93/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_158]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_159,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_541,plain,
% 1.93/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_159]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_542,plain,
% 1.93/0.99      ( sK5 != k1_xboole_0
% 1.93/0.99      | k1_xboole_0 = sK5
% 1.93/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_541]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_543,plain,
% 1.93/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_159]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_544,plain,
% 1.93/0.99      ( sK4 != k1_xboole_0
% 1.93/0.99      | k1_xboole_0 = sK4
% 1.93/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_543]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_545,plain,
% 1.93/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_159]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_546,plain,
% 1.93/0.99      ( sK3 != k1_xboole_0
% 1.93/0.99      | k1_xboole_0 = sK3
% 1.93/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_545]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2112,plain,
% 1.93/0.99      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK1(sK3,sK4,sK5,sK7)),sK2(sK3,sK4,sK5,sK7)) = sK7 ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_2038,c_14,c_13,c_12,c_177,c_542,c_544,c_546]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_15,negated_conjecture,
% 1.93/0.99      ( ~ m1_subset_1(X0,sK5)
% 1.93/0.99      | ~ m1_subset_1(X1,sK4)
% 1.93/0.99      | ~ m1_subset_1(X2,sK3)
% 1.93/0.99      | k4_tarski(k4_tarski(X2,X1),X0) != sK7
% 1.93/0.99      | sK6 = X1 ),
% 1.93/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_376,plain,
% 1.93/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
% 1.93/0.99      | sK6 = X1
% 1.93/0.99      | m1_subset_1(X2,sK5) != iProver_top
% 1.93/0.99      | m1_subset_1(X1,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(X0,sK3) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2116,plain,
% 1.93/0.99      ( sK1(sK3,sK4,sK5,sK7) = sK6
% 1.93/0.99      | m1_subset_1(sK2(sK3,sK4,sK5,sK7),sK5) != iProver_top
% 1.93/0.99      | m1_subset_1(sK1(sK3,sK4,sK5,sK7),sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_2112,c_376]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_17,plain,
% 1.93/0.99      ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 1.93/0.99      | m1_subset_1(sK2(X1,X2,X3,X0),X3)
% 1.93/0.99      | k1_xboole_0 = X3
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1 ),
% 1.93/0.99      inference(cnf_transformation,[],[f25]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_557,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,sK5))
% 1.93/0.99      | m1_subset_1(sK2(X1,X2,sK5,X0),sK5)
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = sK5 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_723,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK4,sK5))
% 1.93/0.99      | m1_subset_1(sK2(X1,sK4,sK5,X0),sK5)
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = sK5
% 1.93/0.99      | k1_xboole_0 = sK4 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_557]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_986,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(sK3,sK4,sK5))
% 1.93/0.99      | m1_subset_1(sK2(sK3,sK4,sK5,X0),sK5)
% 1.93/0.99      | k1_xboole_0 = sK5
% 1.93/0.99      | k1_xboole_0 = sK4
% 1.93/0.99      | k1_xboole_0 = sK3 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_723]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1934,plain,
% 1.93/0.99      ( m1_subset_1(sK2(sK3,sK4,sK5,sK7),sK5)
% 1.93/0.99      | ~ m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))
% 1.93/0.99      | k1_xboole_0 = sK5
% 1.93/0.99      | k1_xboole_0 = sK4
% 1.93/0.99      | k1_xboole_0 = sK3 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_986]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1935,plain,
% 1.93/0.99      ( k1_xboole_0 = sK5
% 1.93/0.99      | k1_xboole_0 = sK4
% 1.93/0.99      | k1_xboole_0 = sK3
% 1.93/0.99      | m1_subset_1(sK2(sK3,sK4,sK5,sK7),sK5) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2218,plain,
% 1.93/0.99      ( sK1(sK3,sK4,sK5,sK7) = sK6
% 1.93/0.99      | m1_subset_1(sK1(sK3,sK4,sK5,sK7),sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_2116,c_17,c_14,c_13,c_12,c_1935]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2225,plain,
% 1.93/0.99      ( sK1(sK3,sK4,sK5,sK7) = sK6
% 1.93/0.99      | sK5 = k1_xboole_0
% 1.93/0.99      | sK4 = k1_xboole_0
% 1.93/0.99      | sK3 = k1_xboole_0
% 1.93/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_384,c_2218]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2231,plain,
% 1.93/0.99      ( m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top
% 1.93/0.99      | sK1(sK3,sK4,sK5,sK7) = sK6 ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_2225,c_17,c_14,c_13,c_12,c_177,c_542,c_544,c_546]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2232,plain,
% 1.93/0.99      ( sK1(sK3,sK4,sK5,sK7) = sK6
% 1.93/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,sK7),sK3) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_2231]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2237,plain,
% 1.93/0.99      ( sK1(sK3,sK4,sK5,sK7) = sK6
% 1.93/0.99      | sK5 = k1_xboole_0
% 1.93/0.99      | sK4 = k1_xboole_0
% 1.93/0.99      | sK3 = k1_xboole_0
% 1.93/0.99      | m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_383,c_2232]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2240,plain,
% 1.93/0.99      ( sK1(sK3,sK4,sK5,sK7) = sK6 ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_2237,c_17,c_14,c_13,c_12,c_177,c_542,c_544,c_546]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2243,plain,
% 1.93/0.99      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK6),sK2(sK3,sK4,sK5,sK7)) = sK7 ),
% 1.93/0.99      inference(demodulation,[status(thm)],[c_2240,c_2112]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_9,plain,
% 1.93/0.99      ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k3_zfmisc_1(X3,X4,X5))
% 1.93/0.99      | k6_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X1
% 1.93/0.99      | k1_xboole_0 = X5
% 1.93/0.99      | k1_xboole_0 = X4
% 1.93/0.99      | k1_xboole_0 = X3 ),
% 1.93/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_378,plain,
% 1.93/0.99      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
% 1.93/0.99      | k1_xboole_0 = X0
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2285,plain,
% 1.93/0.99      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,sK7),sK6),sK2(sK3,sK4,sK5,sK7))) = sK6
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = X0
% 1.93/0.99      | m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_2243,c_378]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2298,plain,
% 1.93/0.99      ( k6_mcart_1(X0,X1,X2,sK7) = sK6
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = X0
% 1.93/0.99      | m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_2285,c_2243]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3037,plain,
% 1.93/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) = sK6
% 1.93/0.99      | sK5 = k1_xboole_0
% 1.93/0.99      | sK4 = k1_xboole_0
% 1.93/0.99      | sK3 = k1_xboole_0 ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_375,c_2298]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 1.93/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 1.93/0.99      | k1_xboole_0 = X3
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | k1_xboole_0 = X1 ),
% 1.93/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_381,plain,
% 1.93/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 1.93/0.99      | k1_xboole_0 = X1
% 1.93/0.99      | k1_xboole_0 = X0
% 1.93/0.99      | k1_xboole_0 = X2
% 1.93/0.99      | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1208,plain,
% 1.93/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 1.93/0.99      | sK5 = k1_xboole_0
% 1.93/0.99      | sK4 = k1_xboole_0
% 1.93/0.99      | sK3 = k1_xboole_0 ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_375,c_381]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1690,plain,
% 1.93/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_1208,c_14,c_13,c_12,c_177,c_542,c_544,c_546]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3038,plain,
% 1.93/0.99      ( k2_mcart_1(k1_mcart_1(sK7)) = sK6
% 1.93/0.99      | sK5 = k1_xboole_0
% 1.93/0.99      | sK4 = k1_xboole_0
% 1.93/0.99      | sK3 = k1_xboole_0 ),
% 1.93/0.99      inference(demodulation,[status(thm)],[c_3037,c_1690]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_11,negated_conjecture,
% 1.93/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
% 1.93/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1693,plain,
% 1.93/0.99      ( k2_mcart_1(k1_mcart_1(sK7)) != sK6 ),
% 1.93/0.99      inference(demodulation,[status(thm)],[c_1690,c_11]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(contradiction,plain,
% 1.93/0.99      ( $false ),
% 1.93/0.99      inference(minisat,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_3038,c_1693,c_546,c_544,c_542,c_177,c_12,c_13,c_14]) ).
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  ------                               Statistics
% 1.93/0.99  
% 1.93/0.99  ------ General
% 1.93/0.99  
% 1.93/0.99  abstr_ref_over_cycles:                  0
% 1.93/0.99  abstr_ref_under_cycles:                 0
% 1.93/0.99  gc_basic_clause_elim:                   0
% 1.93/0.99  forced_gc_time:                         0
% 1.93/0.99  parsing_time:                           0.01
% 1.93/0.99  unif_index_cands_time:                  0.
% 1.93/0.99  unif_index_add_time:                    0.
% 1.93/0.99  orderings_time:                         0.
% 1.93/0.99  out_proof_time:                         0.009
% 1.93/0.99  total_time:                             0.13
% 1.93/0.99  num_of_symbols:                         48
% 1.93/0.99  num_of_terms:                           4682
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing
% 1.93/0.99  
% 1.93/0.99  num_of_splits:                          0
% 1.93/0.99  num_of_split_atoms:                     0
% 1.93/0.99  num_of_reused_defs:                     0
% 1.93/0.99  num_eq_ax_congr_red:                    36
% 1.93/0.99  num_of_sem_filtered_clauses:            1
% 1.93/0.99  num_of_subtypes:                        0
% 1.93/0.99  monotx_restored_types:                  0
% 1.93/0.99  sat_num_of_epr_types:                   0
% 1.93/0.99  sat_num_of_non_cyclic_types:            0
% 1.93/0.99  sat_guarded_non_collapsed_types:        0
% 1.93/0.99  num_pure_diseq_elim:                    0
% 1.93/0.99  simp_replaced_by:                       0
% 1.93/0.99  res_preprocessed:                       72
% 1.93/0.99  prep_upred:                             0
% 1.93/0.99  prep_unflattend:                        0
% 1.93/0.99  smt_new_axioms:                         0
% 1.93/0.99  pred_elim_cands:                        1
% 1.93/0.99  pred_elim:                              0
% 1.93/0.99  pred_elim_cl:                           0
% 1.93/0.99  pred_elim_cycles:                       1
% 1.93/0.99  merged_defs:                            0
% 1.93/0.99  merged_defs_ncl:                        0
% 1.93/0.99  bin_hyper_res:                          0
% 1.93/0.99  prep_cycles:                            3
% 1.93/0.99  pred_elim_time:                         0.
% 1.93/0.99  splitting_time:                         0.
% 1.93/0.99  sem_filter_time:                        0.
% 1.93/0.99  monotx_time:                            0.
% 1.93/0.99  subtype_inf_time:                       0.
% 1.93/0.99  
% 1.93/0.99  ------ Problem properties
% 1.93/0.99  
% 1.93/0.99  clauses:                                17
% 1.93/0.99  conjectures:                            6
% 1.93/0.99  epr:                                    3
% 1.93/0.99  horn:                                   7
% 1.93/0.99  ground:                                 5
% 1.93/0.99  unary:                                  5
% 1.93/0.99  binary:                                 1
% 1.93/0.99  lits:                                   62
% 1.93/0.99  lits_eq:                                43
% 1.93/0.99  fd_pure:                                0
% 1.93/0.99  fd_pseudo:                              0
% 1.93/0.99  fd_cond:                                7
% 1.93/0.99  fd_pseudo_cond:                         0
% 1.93/0.99  ac_symbols:                             0
% 1.93/0.99  
% 1.93/0.99  ------ Propositional Solver
% 1.93/0.99  
% 1.93/0.99  prop_solver_calls:                      21
% 1.93/0.99  prop_fast_solver_calls:                 698
% 1.93/0.99  smt_solver_calls:                       0
% 1.93/0.99  smt_fast_solver_calls:                  0
% 1.93/0.99  prop_num_of_clauses:                    1091
% 1.93/0.99  prop_preprocess_simplified:             4005
% 1.93/0.99  prop_fo_subsumed:                       36
% 1.93/0.99  prop_solver_time:                       0.
% 1.93/0.99  smt_solver_time:                        0.
% 1.93/0.99  smt_fast_solver_time:                   0.
% 1.93/0.99  prop_fast_solver_time:                  0.
% 1.93/0.99  prop_unsat_core_time:                   0.
% 1.93/0.99  
% 1.93/0.99  ------ QBF
% 1.93/0.99  
% 1.93/0.99  qbf_q_res:                              0
% 1.93/0.99  qbf_num_tautologies:                    0
% 1.93/0.99  qbf_prep_cycles:                        0
% 1.93/0.99  
% 1.93/0.99  ------ BMC1
% 1.93/0.99  
% 1.93/0.99  bmc1_current_bound:                     -1
% 1.93/0.99  bmc1_last_solved_bound:                 -1
% 1.93/0.99  bmc1_unsat_core_size:                   -1
% 1.93/0.99  bmc1_unsat_core_parents_size:           -1
% 1.93/0.99  bmc1_merge_next_fun:                    0
% 1.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation
% 1.93/0.99  
% 1.93/0.99  inst_num_of_clauses:                    317
% 1.93/0.99  inst_num_in_passive:                    18
% 1.93/0.99  inst_num_in_active:                     220
% 1.93/0.99  inst_num_in_unprocessed:                79
% 1.93/0.99  inst_num_of_loops:                      220
% 1.93/0.99  inst_num_of_learning_restarts:          0
% 1.93/0.99  inst_num_moves_active_passive:          0
% 1.93/0.99  inst_lit_activity:                      0
% 1.93/0.99  inst_lit_activity_moves:                0
% 1.93/0.99  inst_num_tautologies:                   0
% 1.93/0.99  inst_num_prop_implied:                  0
% 1.93/0.99  inst_num_existing_simplified:           0
% 1.93/0.99  inst_num_eq_res_simplified:             0
% 1.93/0.99  inst_num_child_elim:                    0
% 1.93/0.99  inst_num_of_dismatching_blockings:      0
% 1.93/0.99  inst_num_of_non_proper_insts:           281
% 1.93/0.99  inst_num_of_duplicates:                 0
% 1.93/0.99  inst_inst_num_from_inst_to_res:         0
% 1.93/0.99  inst_dismatching_checking_time:         0.
% 1.93/0.99  
% 1.93/0.99  ------ Resolution
% 1.93/0.99  
% 1.93/0.99  res_num_of_clauses:                     0
% 1.93/0.99  res_num_in_passive:                     0
% 1.93/0.99  res_num_in_active:                      0
% 1.93/0.99  res_num_of_loops:                       75
% 1.93/0.99  res_forward_subset_subsumed:            4
% 1.93/0.99  res_backward_subset_subsumed:           0
% 1.93/0.99  res_forward_subsumed:                   0
% 1.93/0.99  res_backward_subsumed:                  0
% 1.93/0.99  res_forward_subsumption_resolution:     0
% 1.93/0.99  res_backward_subsumption_resolution:    0
% 1.93/0.99  res_clause_to_clause_subsumption:       204
% 1.93/0.99  res_orphan_elimination:                 0
% 1.93/0.99  res_tautology_del:                      0
% 1.93/0.99  res_num_eq_res_simplified:              0
% 1.93/0.99  res_num_sel_changes:                    0
% 1.93/0.99  res_moves_from_active_to_pass:          0
% 1.93/0.99  
% 1.93/0.99  ------ Superposition
% 1.93/0.99  
% 1.93/0.99  sup_time_total:                         0.
% 1.93/0.99  sup_time_generating:                    0.
% 1.93/0.99  sup_time_sim_full:                      0.
% 1.93/0.99  sup_time_sim_immed:                     0.
% 1.93/0.99  
% 1.93/0.99  sup_num_of_clauses:                     64
% 1.93/0.99  sup_num_in_active:                      35
% 1.93/0.99  sup_num_in_passive:                     29
% 1.93/0.99  sup_num_of_loops:                       42
% 1.93/0.99  sup_fw_superposition:                   28
% 1.93/0.99  sup_bw_superposition:                   37
% 1.93/0.99  sup_immediate_simplified:               24
% 1.93/0.99  sup_given_eliminated:                   0
% 1.93/0.99  comparisons_done:                       0
% 1.93/0.99  comparisons_avoided:                    57
% 1.93/0.99  
% 1.93/0.99  ------ Simplifications
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  sim_fw_subset_subsumed:                 1
% 1.93/0.99  sim_bw_subset_subsumed:                 2
% 1.93/0.99  sim_fw_subsumed:                        2
% 1.93/0.99  sim_bw_subsumed:                        0
% 1.93/0.99  sim_fw_subsumption_res:                 0
% 1.93/0.99  sim_bw_subsumption_res:                 0
% 1.93/0.99  sim_tautology_del:                      0
% 1.93/0.99  sim_eq_tautology_del:                   2
% 1.93/0.99  sim_eq_res_simp:                        0
% 1.93/0.99  sim_fw_demodulated:                     2
% 1.93/0.99  sim_bw_demodulated:                     6
% 1.93/0.99  sim_light_normalised:                   26
% 1.93/0.99  sim_joinable_taut:                      0
% 1.93/0.99  sim_joinable_simp:                      0
% 1.93/0.99  sim_ac_normalised:                      0
% 1.93/0.99  sim_smt_subsumption:                    0
% 1.93/0.99  
%------------------------------------------------------------------------------
