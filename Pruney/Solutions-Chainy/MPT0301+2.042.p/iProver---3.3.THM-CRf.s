%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:02 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 391 expanded)
%              Number of clauses        :   45 ( 139 expanded)
%              Number of leaves         :   10 (  94 expanded)
%              Depth                    :   22
%              Number of atoms          :  297 (1836 expanded)
%              Number of equality atoms :  178 ( 923 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f16,f15,f14])).

fof(f27,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f26,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK7
          & k1_xboole_0 != sK6 )
        | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
      & ( k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ( k1_xboole_0 != sK7
        & k1_xboole_0 != sK6 )
      | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f20,f21])).

fof(f36,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f40,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f37,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_494,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_484,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_643,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_484])).

cnf(c_826,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_643])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_487,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_800,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_487,c_643])).

cnf(c_3448,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_826,c_800])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_486,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_910,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_486,c_800])).

cnf(c_3451,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_826,c_910])).

cnf(c_3463,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3448,c_3451])).

cnf(c_5,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_491,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_489,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1503,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_489])).

cnf(c_1994,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1503,c_643])).

cnf(c_1999,plain,
    ( k2_zfmisc_1(X0,X1) = sK6
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X2,sK7) != iProver_top
    | r2_hidden(sK3(X0,X1,sK6),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_491,c_1994])).

cnf(c_1044,plain,
    ( ~ r2_hidden(sK0(X0,sK7),X0)
    | k4_xboole_0(X0,k1_tarski(sK0(X0,sK7))) != X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1045,plain,
    ( k4_xboole_0(X0,k1_tarski(sK0(X0,sK7))) != X0
    | r2_hidden(sK0(X0,sK7),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_1047,plain,
    ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(k1_xboole_0,sK7))) != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1257,plain,
    ( ~ r2_hidden(sK0(sK6,k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_tarski(sK0(sK6,k1_xboole_0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1258,plain,
    ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(sK6,k1_xboole_0))) != k1_xboole_0
    | r2_hidden(sK0(sK6,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_2593,plain,
    ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(k1_xboole_0,sK7))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2716,plain,
    ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(sK6,k1_xboole_0))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2007,plain,
    ( sK6 = X0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_1994])).

cnf(c_3074,plain,
    ( sK6 = X0
    | sK6 = k1_xboole_0
    | sK7 = X1
    | sK7 = k1_xboole_0
    | r2_hidden(sK0(X1,sK7),X1) = iProver_top
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_2007])).

cnf(c_3215,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(sK0(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3074])).

cnf(c_3221,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1999,c_1047,c_1258,c_2593,c_2716,c_3215])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3226,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3221,c_14])).

cnf(c_3231,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3226,c_3221])).

cnf(c_7323,plain,
    ( sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3463,c_3231])).

cnf(c_7335,plain,
    ( sK7 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7323])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7660,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7335,c_13])).

cnf(c_7661,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7660])).

cnf(c_7663,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7661,c_3448])).

cnf(c_7664,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7663])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:53:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.91/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/1.00  
% 2.91/1.00  ------  iProver source info
% 2.91/1.00  
% 2.91/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.91/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/1.00  git: non_committed_changes: false
% 2.91/1.00  git: last_make_outside_of_git: false
% 2.91/1.00  
% 2.91/1.00  ------ 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options
% 2.91/1.00  
% 2.91/1.00  --out_options                           all
% 2.91/1.00  --tptp_safe_out                         true
% 2.91/1.00  --problem_path                          ""
% 2.91/1.00  --include_path                          ""
% 2.91/1.00  --clausifier                            res/vclausify_rel
% 2.91/1.00  --clausifier_options                    --mode clausify
% 2.91/1.00  --stdin                                 false
% 2.91/1.00  --stats_out                             all
% 2.91/1.00  
% 2.91/1.00  ------ General Options
% 2.91/1.00  
% 2.91/1.00  --fof                                   false
% 2.91/1.00  --time_out_real                         305.
% 2.91/1.00  --time_out_virtual                      -1.
% 2.91/1.00  --symbol_type_check                     false
% 2.91/1.00  --clausify_out                          false
% 2.91/1.00  --sig_cnt_out                           false
% 2.91/1.00  --trig_cnt_out                          false
% 2.91/1.00  --trig_cnt_out_tolerance                1.
% 2.91/1.00  --trig_cnt_out_sk_spl                   false
% 2.91/1.00  --abstr_cl_out                          false
% 2.91/1.00  
% 2.91/1.00  ------ Global Options
% 2.91/1.00  
% 2.91/1.00  --schedule                              default
% 2.91/1.00  --add_important_lit                     false
% 2.91/1.00  --prop_solver_per_cl                    1000
% 2.91/1.00  --min_unsat_core                        false
% 2.91/1.00  --soft_assumptions                      false
% 2.91/1.00  --soft_lemma_size                       3
% 2.91/1.00  --prop_impl_unit_size                   0
% 2.91/1.00  --prop_impl_unit                        []
% 2.91/1.00  --share_sel_clauses                     true
% 2.91/1.00  --reset_solvers                         false
% 2.91/1.00  --bc_imp_inh                            [conj_cone]
% 2.91/1.00  --conj_cone_tolerance                   3.
% 2.91/1.00  --extra_neg_conj                        none
% 2.91/1.00  --large_theory_mode                     true
% 2.91/1.00  --prolific_symb_bound                   200
% 2.91/1.00  --lt_threshold                          2000
% 2.91/1.00  --clause_weak_htbl                      true
% 2.91/1.00  --gc_record_bc_elim                     false
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing Options
% 2.91/1.00  
% 2.91/1.00  --preprocessing_flag                    true
% 2.91/1.00  --time_out_prep_mult                    0.1
% 2.91/1.00  --splitting_mode                        input
% 2.91/1.00  --splitting_grd                         true
% 2.91/1.00  --splitting_cvd                         false
% 2.91/1.00  --splitting_cvd_svl                     false
% 2.91/1.00  --splitting_nvd                         32
% 2.91/1.00  --sub_typing                            true
% 2.91/1.00  --prep_gs_sim                           true
% 2.91/1.00  --prep_unflatten                        true
% 2.91/1.00  --prep_res_sim                          true
% 2.91/1.00  --prep_upred                            true
% 2.91/1.00  --prep_sem_filter                       exhaustive
% 2.91/1.00  --prep_sem_filter_out                   false
% 2.91/1.00  --pred_elim                             true
% 2.91/1.00  --res_sim_input                         true
% 2.91/1.00  --eq_ax_congr_red                       true
% 2.91/1.00  --pure_diseq_elim                       true
% 2.91/1.00  --brand_transform                       false
% 2.91/1.00  --non_eq_to_eq                          false
% 2.91/1.00  --prep_def_merge                        true
% 2.91/1.00  --prep_def_merge_prop_impl              false
% 2.91/1.00  --prep_def_merge_mbd                    true
% 2.91/1.00  --prep_def_merge_tr_red                 false
% 2.91/1.00  --prep_def_merge_tr_cl                  false
% 2.91/1.00  --smt_preprocessing                     true
% 2.91/1.00  --smt_ac_axioms                         fast
% 2.91/1.00  --preprocessed_out                      false
% 2.91/1.00  --preprocessed_stats                    false
% 2.91/1.00  
% 2.91/1.00  ------ Abstraction refinement Options
% 2.91/1.00  
% 2.91/1.00  --abstr_ref                             []
% 2.91/1.00  --abstr_ref_prep                        false
% 2.91/1.00  --abstr_ref_until_sat                   false
% 2.91/1.00  --abstr_ref_sig_restrict                funpre
% 2.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.00  --abstr_ref_under                       []
% 2.91/1.00  
% 2.91/1.00  ------ SAT Options
% 2.91/1.00  
% 2.91/1.00  --sat_mode                              false
% 2.91/1.00  --sat_fm_restart_options                ""
% 2.91/1.00  --sat_gr_def                            false
% 2.91/1.00  --sat_epr_types                         true
% 2.91/1.00  --sat_non_cyclic_types                  false
% 2.91/1.00  --sat_finite_models                     false
% 2.91/1.00  --sat_fm_lemmas                         false
% 2.91/1.00  --sat_fm_prep                           false
% 2.91/1.00  --sat_fm_uc_incr                        true
% 2.91/1.00  --sat_out_model                         small
% 2.91/1.00  --sat_out_clauses                       false
% 2.91/1.00  
% 2.91/1.00  ------ QBF Options
% 2.91/1.00  
% 2.91/1.00  --qbf_mode                              false
% 2.91/1.00  --qbf_elim_univ                         false
% 2.91/1.00  --qbf_dom_inst                          none
% 2.91/1.00  --qbf_dom_pre_inst                      false
% 2.91/1.00  --qbf_sk_in                             false
% 2.91/1.00  --qbf_pred_elim                         true
% 2.91/1.00  --qbf_split                             512
% 2.91/1.00  
% 2.91/1.00  ------ BMC1 Options
% 2.91/1.00  
% 2.91/1.00  --bmc1_incremental                      false
% 2.91/1.00  --bmc1_axioms                           reachable_all
% 2.91/1.00  --bmc1_min_bound                        0
% 2.91/1.00  --bmc1_max_bound                        -1
% 2.91/1.00  --bmc1_max_bound_default                -1
% 2.91/1.00  --bmc1_symbol_reachability              true
% 2.91/1.00  --bmc1_property_lemmas                  false
% 2.91/1.00  --bmc1_k_induction                      false
% 2.91/1.00  --bmc1_non_equiv_states                 false
% 2.91/1.00  --bmc1_deadlock                         false
% 2.91/1.00  --bmc1_ucm                              false
% 2.91/1.00  --bmc1_add_unsat_core                   none
% 2.91/1.00  --bmc1_unsat_core_children              false
% 2.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.00  --bmc1_out_stat                         full
% 2.91/1.00  --bmc1_ground_init                      false
% 2.91/1.00  --bmc1_pre_inst_next_state              false
% 2.91/1.00  --bmc1_pre_inst_state                   false
% 2.91/1.00  --bmc1_pre_inst_reach_state             false
% 2.91/1.00  --bmc1_out_unsat_core                   false
% 2.91/1.00  --bmc1_aig_witness_out                  false
% 2.91/1.00  --bmc1_verbose                          false
% 2.91/1.00  --bmc1_dump_clauses_tptp                false
% 2.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.00  --bmc1_dump_file                        -
% 2.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.00  --bmc1_ucm_extend_mode                  1
% 2.91/1.00  --bmc1_ucm_init_mode                    2
% 2.91/1.00  --bmc1_ucm_cone_mode                    none
% 2.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.00  --bmc1_ucm_relax_model                  4
% 2.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.00  --bmc1_ucm_layered_model                none
% 2.91/1.00  --bmc1_ucm_max_lemma_size               10
% 2.91/1.00  
% 2.91/1.00  ------ AIG Options
% 2.91/1.00  
% 2.91/1.00  --aig_mode                              false
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation Options
% 2.91/1.00  
% 2.91/1.00  --instantiation_flag                    true
% 2.91/1.00  --inst_sos_flag                         false
% 2.91/1.00  --inst_sos_phase                        true
% 2.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel_side                     num_symb
% 2.91/1.00  --inst_solver_per_active                1400
% 2.91/1.00  --inst_solver_calls_frac                1.
% 2.91/1.00  --inst_passive_queue_type               priority_queues
% 2.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.00  --inst_passive_queues_freq              [25;2]
% 2.91/1.00  --inst_dismatching                      true
% 2.91/1.00  --inst_eager_unprocessed_to_passive     true
% 2.91/1.00  --inst_prop_sim_given                   true
% 2.91/1.00  --inst_prop_sim_new                     false
% 2.91/1.00  --inst_subs_new                         false
% 2.91/1.00  --inst_eq_res_simp                      false
% 2.91/1.00  --inst_subs_given                       false
% 2.91/1.00  --inst_orphan_elimination               true
% 2.91/1.00  --inst_learning_loop_flag               true
% 2.91/1.00  --inst_learning_start                   3000
% 2.91/1.00  --inst_learning_factor                  2
% 2.91/1.00  --inst_start_prop_sim_after_learn       3
% 2.91/1.00  --inst_sel_renew                        solver
% 2.91/1.00  --inst_lit_activity_flag                true
% 2.91/1.00  --inst_restr_to_given                   false
% 2.91/1.00  --inst_activity_threshold               500
% 2.91/1.00  --inst_out_proof                        true
% 2.91/1.00  
% 2.91/1.00  ------ Resolution Options
% 2.91/1.00  
% 2.91/1.00  --resolution_flag                       true
% 2.91/1.00  --res_lit_sel                           adaptive
% 2.91/1.00  --res_lit_sel_side                      none
% 2.91/1.00  --res_ordering                          kbo
% 2.91/1.00  --res_to_prop_solver                    active
% 2.91/1.00  --res_prop_simpl_new                    false
% 2.91/1.00  --res_prop_simpl_given                  true
% 2.91/1.00  --res_passive_queue_type                priority_queues
% 2.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.00  --res_passive_queues_freq               [15;5]
% 2.91/1.00  --res_forward_subs                      full
% 2.91/1.00  --res_backward_subs                     full
% 2.91/1.00  --res_forward_subs_resolution           true
% 2.91/1.00  --res_backward_subs_resolution          true
% 2.91/1.00  --res_orphan_elimination                true
% 2.91/1.00  --res_time_limit                        2.
% 2.91/1.00  --res_out_proof                         true
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Options
% 2.91/1.00  
% 2.91/1.00  --superposition_flag                    true
% 2.91/1.00  --sup_passive_queue_type                priority_queues
% 2.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.00  --demod_completeness_check              fast
% 2.91/1.00  --demod_use_ground                      true
% 2.91/1.00  --sup_to_prop_solver                    passive
% 2.91/1.00  --sup_prop_simpl_new                    true
% 2.91/1.00  --sup_prop_simpl_given                  true
% 2.91/1.00  --sup_fun_splitting                     false
% 2.91/1.00  --sup_smt_interval                      50000
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Simplification Setup
% 2.91/1.00  
% 2.91/1.00  --sup_indices_passive                   []
% 2.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_full_bw                           [BwDemod]
% 2.91/1.00  --sup_immed_triv                        [TrivRules]
% 2.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_immed_bw_main                     []
% 2.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  
% 2.91/1.00  ------ Combination Options
% 2.91/1.00  
% 2.91/1.00  --comb_res_mult                         3
% 2.91/1.00  --comb_sup_mult                         2
% 2.91/1.00  --comb_inst_mult                        10
% 2.91/1.00  
% 2.91/1.00  ------ Debug Options
% 2.91/1.00  
% 2.91/1.00  --dbg_backtrace                         false
% 2.91/1.00  --dbg_dump_prop_clauses                 false
% 2.91/1.00  --dbg_dump_prop_clauses_file            -
% 2.91/1.00  --dbg_out_stat                          false
% 2.91/1.00  ------ Parsing...
% 2.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.91/1.00  ------ Proving...
% 2.91/1.00  ------ Problem Properties 
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  clauses                                 16
% 2.91/1.00  conjectures                             3
% 2.91/1.00  EPR                                     0
% 2.91/1.00  Horn                                    10
% 2.91/1.00  unary                                   1
% 2.91/1.00  binary                                  7
% 2.91/1.00  lits                                    41
% 2.91/1.00  lits eq                                 19
% 2.91/1.00  fd_pure                                 0
% 2.91/1.00  fd_pseudo                               0
% 2.91/1.00  fd_cond                                 0
% 2.91/1.00  fd_pseudo_cond                          6
% 2.91/1.00  AC symbols                              0
% 2.91/1.00  
% 2.91/1.00  ------ Schedule dynamic 5 is on 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  ------ 
% 2.91/1.00  Current options:
% 2.91/1.00  ------ 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options
% 2.91/1.00  
% 2.91/1.00  --out_options                           all
% 2.91/1.00  --tptp_safe_out                         true
% 2.91/1.00  --problem_path                          ""
% 2.91/1.00  --include_path                          ""
% 2.91/1.00  --clausifier                            res/vclausify_rel
% 2.91/1.00  --clausifier_options                    --mode clausify
% 2.91/1.00  --stdin                                 false
% 2.91/1.00  --stats_out                             all
% 2.91/1.00  
% 2.91/1.00  ------ General Options
% 2.91/1.00  
% 2.91/1.00  --fof                                   false
% 2.91/1.00  --time_out_real                         305.
% 2.91/1.00  --time_out_virtual                      -1.
% 2.91/1.00  --symbol_type_check                     false
% 2.91/1.00  --clausify_out                          false
% 2.91/1.00  --sig_cnt_out                           false
% 2.91/1.00  --trig_cnt_out                          false
% 2.91/1.00  --trig_cnt_out_tolerance                1.
% 2.91/1.00  --trig_cnt_out_sk_spl                   false
% 2.91/1.00  --abstr_cl_out                          false
% 2.91/1.00  
% 2.91/1.00  ------ Global Options
% 2.91/1.00  
% 2.91/1.00  --schedule                              default
% 2.91/1.00  --add_important_lit                     false
% 2.91/1.00  --prop_solver_per_cl                    1000
% 2.91/1.00  --min_unsat_core                        false
% 2.91/1.00  --soft_assumptions                      false
% 2.91/1.00  --soft_lemma_size                       3
% 2.91/1.00  --prop_impl_unit_size                   0
% 2.91/1.00  --prop_impl_unit                        []
% 2.91/1.00  --share_sel_clauses                     true
% 2.91/1.00  --reset_solvers                         false
% 2.91/1.00  --bc_imp_inh                            [conj_cone]
% 2.91/1.00  --conj_cone_tolerance                   3.
% 2.91/1.00  --extra_neg_conj                        none
% 2.91/1.00  --large_theory_mode                     true
% 2.91/1.00  --prolific_symb_bound                   200
% 2.91/1.00  --lt_threshold                          2000
% 2.91/1.00  --clause_weak_htbl                      true
% 2.91/1.00  --gc_record_bc_elim                     false
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing Options
% 2.91/1.00  
% 2.91/1.00  --preprocessing_flag                    true
% 2.91/1.00  --time_out_prep_mult                    0.1
% 2.91/1.00  --splitting_mode                        input
% 2.91/1.00  --splitting_grd                         true
% 2.91/1.00  --splitting_cvd                         false
% 2.91/1.00  --splitting_cvd_svl                     false
% 2.91/1.00  --splitting_nvd                         32
% 2.91/1.00  --sub_typing                            true
% 2.91/1.00  --prep_gs_sim                           true
% 2.91/1.00  --prep_unflatten                        true
% 2.91/1.00  --prep_res_sim                          true
% 2.91/1.00  --prep_upred                            true
% 2.91/1.00  --prep_sem_filter                       exhaustive
% 2.91/1.00  --prep_sem_filter_out                   false
% 2.91/1.00  --pred_elim                             true
% 2.91/1.00  --res_sim_input                         true
% 2.91/1.00  --eq_ax_congr_red                       true
% 2.91/1.00  --pure_diseq_elim                       true
% 2.91/1.00  --brand_transform                       false
% 2.91/1.00  --non_eq_to_eq                          false
% 2.91/1.00  --prep_def_merge                        true
% 2.91/1.00  --prep_def_merge_prop_impl              false
% 2.91/1.00  --prep_def_merge_mbd                    true
% 2.91/1.00  --prep_def_merge_tr_red                 false
% 2.91/1.00  --prep_def_merge_tr_cl                  false
% 2.91/1.00  --smt_preprocessing                     true
% 2.91/1.00  --smt_ac_axioms                         fast
% 2.91/1.00  --preprocessed_out                      false
% 2.91/1.00  --preprocessed_stats                    false
% 2.91/1.00  
% 2.91/1.00  ------ Abstraction refinement Options
% 2.91/1.00  
% 2.91/1.00  --abstr_ref                             []
% 2.91/1.00  --abstr_ref_prep                        false
% 2.91/1.00  --abstr_ref_until_sat                   false
% 2.91/1.00  --abstr_ref_sig_restrict                funpre
% 2.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.00  --abstr_ref_under                       []
% 2.91/1.00  
% 2.91/1.00  ------ SAT Options
% 2.91/1.00  
% 2.91/1.00  --sat_mode                              false
% 2.91/1.00  --sat_fm_restart_options                ""
% 2.91/1.00  --sat_gr_def                            false
% 2.91/1.00  --sat_epr_types                         true
% 2.91/1.00  --sat_non_cyclic_types                  false
% 2.91/1.00  --sat_finite_models                     false
% 2.91/1.00  --sat_fm_lemmas                         false
% 2.91/1.00  --sat_fm_prep                           false
% 2.91/1.00  --sat_fm_uc_incr                        true
% 2.91/1.00  --sat_out_model                         small
% 2.91/1.00  --sat_out_clauses                       false
% 2.91/1.00  
% 2.91/1.00  ------ QBF Options
% 2.91/1.00  
% 2.91/1.00  --qbf_mode                              false
% 2.91/1.00  --qbf_elim_univ                         false
% 2.91/1.00  --qbf_dom_inst                          none
% 2.91/1.00  --qbf_dom_pre_inst                      false
% 2.91/1.00  --qbf_sk_in                             false
% 2.91/1.00  --qbf_pred_elim                         true
% 2.91/1.00  --qbf_split                             512
% 2.91/1.00  
% 2.91/1.00  ------ BMC1 Options
% 2.91/1.00  
% 2.91/1.00  --bmc1_incremental                      false
% 2.91/1.00  --bmc1_axioms                           reachable_all
% 2.91/1.00  --bmc1_min_bound                        0
% 2.91/1.00  --bmc1_max_bound                        -1
% 2.91/1.00  --bmc1_max_bound_default                -1
% 2.91/1.00  --bmc1_symbol_reachability              true
% 2.91/1.00  --bmc1_property_lemmas                  false
% 2.91/1.00  --bmc1_k_induction                      false
% 2.91/1.00  --bmc1_non_equiv_states                 false
% 2.91/1.00  --bmc1_deadlock                         false
% 2.91/1.00  --bmc1_ucm                              false
% 2.91/1.00  --bmc1_add_unsat_core                   none
% 2.91/1.00  --bmc1_unsat_core_children              false
% 2.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.00  --bmc1_out_stat                         full
% 2.91/1.00  --bmc1_ground_init                      false
% 2.91/1.00  --bmc1_pre_inst_next_state              false
% 2.91/1.00  --bmc1_pre_inst_state                   false
% 2.91/1.00  --bmc1_pre_inst_reach_state             false
% 2.91/1.00  --bmc1_out_unsat_core                   false
% 2.91/1.00  --bmc1_aig_witness_out                  false
% 2.91/1.00  --bmc1_verbose                          false
% 2.91/1.00  --bmc1_dump_clauses_tptp                false
% 2.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.00  --bmc1_dump_file                        -
% 2.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.00  --bmc1_ucm_extend_mode                  1
% 2.91/1.00  --bmc1_ucm_init_mode                    2
% 2.91/1.00  --bmc1_ucm_cone_mode                    none
% 2.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.00  --bmc1_ucm_relax_model                  4
% 2.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.00  --bmc1_ucm_layered_model                none
% 2.91/1.00  --bmc1_ucm_max_lemma_size               10
% 2.91/1.00  
% 2.91/1.00  ------ AIG Options
% 2.91/1.00  
% 2.91/1.00  --aig_mode                              false
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation Options
% 2.91/1.00  
% 2.91/1.00  --instantiation_flag                    true
% 2.91/1.00  --inst_sos_flag                         false
% 2.91/1.00  --inst_sos_phase                        true
% 2.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel_side                     none
% 2.91/1.00  --inst_solver_per_active                1400
% 2.91/1.00  --inst_solver_calls_frac                1.
% 2.91/1.00  --inst_passive_queue_type               priority_queues
% 2.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.00  --inst_passive_queues_freq              [25;2]
% 2.91/1.00  --inst_dismatching                      true
% 2.91/1.00  --inst_eager_unprocessed_to_passive     true
% 2.91/1.00  --inst_prop_sim_given                   true
% 2.91/1.00  --inst_prop_sim_new                     false
% 2.91/1.00  --inst_subs_new                         false
% 2.91/1.00  --inst_eq_res_simp                      false
% 2.91/1.00  --inst_subs_given                       false
% 2.91/1.00  --inst_orphan_elimination               true
% 2.91/1.00  --inst_learning_loop_flag               true
% 2.91/1.00  --inst_learning_start                   3000
% 2.91/1.00  --inst_learning_factor                  2
% 2.91/1.00  --inst_start_prop_sim_after_learn       3
% 2.91/1.00  --inst_sel_renew                        solver
% 2.91/1.00  --inst_lit_activity_flag                true
% 2.91/1.00  --inst_restr_to_given                   false
% 2.91/1.00  --inst_activity_threshold               500
% 2.91/1.00  --inst_out_proof                        true
% 2.91/1.00  
% 2.91/1.00  ------ Resolution Options
% 2.91/1.00  
% 2.91/1.00  --resolution_flag                       false
% 2.91/1.00  --res_lit_sel                           adaptive
% 2.91/1.00  --res_lit_sel_side                      none
% 2.91/1.00  --res_ordering                          kbo
% 2.91/1.00  --res_to_prop_solver                    active
% 2.91/1.00  --res_prop_simpl_new                    false
% 2.91/1.00  --res_prop_simpl_given                  true
% 2.91/1.00  --res_passive_queue_type                priority_queues
% 2.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.00  --res_passive_queues_freq               [15;5]
% 2.91/1.00  --res_forward_subs                      full
% 2.91/1.00  --res_backward_subs                     full
% 2.91/1.00  --res_forward_subs_resolution           true
% 2.91/1.00  --res_backward_subs_resolution          true
% 2.91/1.00  --res_orphan_elimination                true
% 2.91/1.00  --res_time_limit                        2.
% 2.91/1.00  --res_out_proof                         true
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Options
% 2.91/1.00  
% 2.91/1.00  --superposition_flag                    true
% 2.91/1.00  --sup_passive_queue_type                priority_queues
% 2.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.00  --demod_completeness_check              fast
% 2.91/1.00  --demod_use_ground                      true
% 2.91/1.00  --sup_to_prop_solver                    passive
% 2.91/1.00  --sup_prop_simpl_new                    true
% 2.91/1.00  --sup_prop_simpl_given                  true
% 2.91/1.00  --sup_fun_splitting                     false
% 2.91/1.00  --sup_smt_interval                      50000
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Simplification Setup
% 2.91/1.00  
% 2.91/1.00  --sup_indices_passive                   []
% 2.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_full_bw                           [BwDemod]
% 2.91/1.00  --sup_immed_triv                        [TrivRules]
% 2.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_immed_bw_main                     []
% 2.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  
% 2.91/1.00  ------ Combination Options
% 2.91/1.00  
% 2.91/1.00  --comb_res_mult                         3
% 2.91/1.00  --comb_sup_mult                         2
% 2.91/1.00  --comb_inst_mult                        10
% 2.91/1.00  
% 2.91/1.00  ------ Debug Options
% 2.91/1.00  
% 2.91/1.00  --dbg_backtrace                         false
% 2.91/1.00  --dbg_dump_prop_clauses                 false
% 2.91/1.00  --dbg_dump_prop_clauses_file            -
% 2.91/1.00  --dbg_out_stat                          false
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  ------ Proving...
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  % SZS status Theorem for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00   Resolution empty clause
% 2.91/1.00  
% 2.91/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  fof(f1,axiom,(
% 2.91/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f7,plain,(
% 2.91/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.91/1.00    inference(ennf_transformation,[],[f1])).
% 2.91/1.00  
% 2.91/1.00  fof(f9,plain,(
% 2.91/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.91/1.00    inference(nnf_transformation,[],[f7])).
% 2.91/1.00  
% 2.91/1.00  fof(f10,plain,(
% 2.91/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f11,plain,(
% 2.91/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 2.91/1.00  
% 2.91/1.00  fof(f23,plain,(
% 2.91/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f11])).
% 2.91/1.00  
% 2.91/1.00  fof(f2,axiom,(
% 2.91/1.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f25,plain,(
% 2.91/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f2])).
% 2.91/1.00  
% 2.91/1.00  fof(f4,axiom,(
% 2.91/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f18,plain,(
% 2.91/1.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.91/1.00    inference(nnf_transformation,[],[f4])).
% 2.91/1.00  
% 2.91/1.00  fof(f34,plain,(
% 2.91/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 2.91/1.00    inference(cnf_transformation,[],[f18])).
% 2.91/1.00  
% 2.91/1.00  fof(f3,axiom,(
% 2.91/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f12,plain,(
% 2.91/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.91/1.00    inference(nnf_transformation,[],[f3])).
% 2.91/1.00  
% 2.91/1.00  fof(f13,plain,(
% 2.91/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.91/1.00    inference(rectify,[],[f12])).
% 2.91/1.00  
% 2.91/1.00  fof(f16,plain,(
% 2.91/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f15,plain,(
% 2.91/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f14,plain,(
% 2.91/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f17,plain,(
% 2.91/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f16,f15,f14])).
% 2.91/1.00  
% 2.91/1.00  fof(f27,plain,(
% 2.91/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.91/1.00    inference(cnf_transformation,[],[f17])).
% 2.91/1.00  
% 2.91/1.00  fof(f42,plain,(
% 2.91/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.91/1.00    inference(equality_resolution,[],[f27])).
% 2.91/1.00  
% 2.91/1.00  fof(f26,plain,(
% 2.91/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.91/1.00    inference(cnf_transformation,[],[f17])).
% 2.91/1.00  
% 2.91/1.00  fof(f43,plain,(
% 2.91/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.91/1.00    inference(equality_resolution,[],[f26])).
% 2.91/1.00  
% 2.91/1.00  fof(f31,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f17])).
% 2.91/1.00  
% 2.91/1.00  fof(f5,conjecture,(
% 2.91/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f6,negated_conjecture,(
% 2.91/1.00    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.91/1.00    inference(negated_conjecture,[],[f5])).
% 2.91/1.00  
% 2.91/1.00  fof(f8,plain,(
% 2.91/1.00    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f6])).
% 2.91/1.00  
% 2.91/1.00  fof(f19,plain,(
% 2.91/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.91/1.00    inference(nnf_transformation,[],[f8])).
% 2.91/1.00  
% 2.91/1.00  fof(f20,plain,(
% 2.91/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.91/1.00    inference(flattening,[],[f19])).
% 2.91/1.00  
% 2.91/1.00  fof(f21,plain,(
% 2.91/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f22,plain,(
% 2.91/1.00    ((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7))),
% 2.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f20,f21])).
% 2.91/1.00  
% 2.91/1.00  fof(f36,plain,(
% 2.91/1.00    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 2.91/1.00    inference(cnf_transformation,[],[f22])).
% 2.91/1.00  
% 2.91/1.00  fof(f29,plain,(
% 2.91/1.00    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.91/1.00    inference(cnf_transformation,[],[f17])).
% 2.91/1.00  
% 2.91/1.00  fof(f39,plain,(
% 2.91/1.00    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.91/1.00    inference(equality_resolution,[],[f29])).
% 2.91/1.00  
% 2.91/1.00  fof(f40,plain,(
% 2.91/1.00    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 2.91/1.00    inference(equality_resolution,[],[f39])).
% 2.91/1.00  
% 2.91/1.00  fof(f37,plain,(
% 2.91/1.00    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 2.91/1.00    inference(cnf_transformation,[],[f22])).
% 2.91/1.00  
% 2.91/1.00  fof(f38,plain,(
% 2.91/1.00    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 2.91/1.00    inference(cnf_transformation,[],[f22])).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1,plain,
% 2.91/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.91/1.00      inference(cnf_transformation,[],[f23]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_494,plain,
% 2.91/1.00      ( X0 = X1
% 2.91/1.00      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.91/1.00      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2,plain,
% 2.91/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.91/1.00      inference(cnf_transformation,[],[f25]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_12,plain,
% 2.91/1.00      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
% 2.91/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_484,plain,
% 2.91/1.00      ( k4_xboole_0(X0,k1_tarski(X1)) != X0 | r2_hidden(X1,X0) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_643,plain,
% 2.91/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2,c_484]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_826,plain,
% 2.91/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_494,c_643]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_9,plain,
% 2.91/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 2.91/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_487,plain,
% 2.91/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.91/1.00      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_800,plain,
% 2.91/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_487,c_643]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3448,plain,
% 2.91/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_826,c_800]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_10,plain,
% 2.91/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_486,plain,
% 2.91/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.91/1.00      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_910,plain,
% 2.91/1.00      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_486,c_800]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3451,plain,
% 2.91/1.00      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_826,c_910]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3463,plain,
% 2.91/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.91/1.00      inference(demodulation,[status(thm)],[c_3448,c_3451]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5,plain,
% 2.91/1.00      ( r2_hidden(sK3(X0,X1,X2),X1)
% 2.91/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.91/1.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 2.91/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_491,plain,
% 2.91/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 2.91/1.00      | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
% 2.91/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_15,negated_conjecture,
% 2.91/1.00      ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
% 2.91/1.00      | k1_xboole_0 = sK6
% 2.91/1.00      | k1_xboole_0 = sK7 ),
% 2.91/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7,plain,
% 2.91/1.00      ( ~ r2_hidden(X0,X1)
% 2.91/1.00      | ~ r2_hidden(X2,X3)
% 2.91/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_489,plain,
% 2.91/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.91/1.00      | r2_hidden(X2,X3) != iProver_top
% 2.91/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1503,plain,
% 2.91/1.00      ( sK6 = k1_xboole_0
% 2.91/1.00      | sK7 = k1_xboole_0
% 2.91/1.00      | r2_hidden(X0,sK6) != iProver_top
% 2.91/1.00      | r2_hidden(X1,sK7) != iProver_top
% 2.91/1.00      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_15,c_489]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1994,plain,
% 2.91/1.00      ( sK6 = k1_xboole_0
% 2.91/1.00      | sK7 = k1_xboole_0
% 2.91/1.00      | r2_hidden(X0,sK6) != iProver_top
% 2.91/1.00      | r2_hidden(X1,sK7) != iProver_top ),
% 2.91/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1503,c_643]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1999,plain,
% 2.91/1.00      ( k2_zfmisc_1(X0,X1) = sK6
% 2.91/1.00      | sK6 = k1_xboole_0
% 2.91/1.00      | sK7 = k1_xboole_0
% 2.91/1.00      | r2_hidden(X2,sK7) != iProver_top
% 2.91/1.00      | r2_hidden(sK3(X0,X1,sK6),X1) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_491,c_1994]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1044,plain,
% 2.91/1.00      ( ~ r2_hidden(sK0(X0,sK7),X0)
% 2.91/1.00      | k4_xboole_0(X0,k1_tarski(sK0(X0,sK7))) != X0 ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1045,plain,
% 2.91/1.00      ( k4_xboole_0(X0,k1_tarski(sK0(X0,sK7))) != X0
% 2.91/1.00      | r2_hidden(sK0(X0,sK7),X0) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1047,plain,
% 2.91/1.00      ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(k1_xboole_0,sK7))) != k1_xboole_0
% 2.91/1.00      | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_1045]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1257,plain,
% 2.91/1.00      ( ~ r2_hidden(sK0(sK6,k1_xboole_0),k1_xboole_0)
% 2.91/1.00      | k4_xboole_0(k1_xboole_0,k1_tarski(sK0(sK6,k1_xboole_0))) != k1_xboole_0 ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1258,plain,
% 2.91/1.00      ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(sK6,k1_xboole_0))) != k1_xboole_0
% 2.91/1.00      | r2_hidden(sK0(sK6,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2593,plain,
% 2.91/1.00      ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(k1_xboole_0,sK7))) = k1_xboole_0 ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2716,plain,
% 2.91/1.00      ( k4_xboole_0(k1_xboole_0,k1_tarski(sK0(sK6,k1_xboole_0))) = k1_xboole_0 ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2007,plain,
% 2.91/1.00      ( sK6 = X0
% 2.91/1.00      | sK6 = k1_xboole_0
% 2.91/1.00      | sK7 = k1_xboole_0
% 2.91/1.00      | r2_hidden(X1,sK7) != iProver_top
% 2.91/1.00      | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_494,c_1994]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3074,plain,
% 2.91/1.00      ( sK6 = X0
% 2.91/1.00      | sK6 = k1_xboole_0
% 2.91/1.00      | sK7 = X1
% 2.91/1.00      | sK7 = k1_xboole_0
% 2.91/1.00      | r2_hidden(sK0(X1,sK7),X1) = iProver_top
% 2.91/1.00      | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_494,c_2007]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3215,plain,
% 2.91/1.00      ( sK6 = k1_xboole_0
% 2.91/1.00      | sK7 = k1_xboole_0
% 2.91/1.00      | r2_hidden(sK0(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
% 2.91/1.00      | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_3074]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3221,plain,
% 2.91/1.00      ( sK6 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_1999,c_1047,c_1258,c_2593,c_2716,c_3215]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_14,negated_conjecture,
% 2.91/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK6 ),
% 2.91/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3226,plain,
% 2.91/1.00      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
% 2.91/1.00      | sK6 != k1_xboole_0
% 2.91/1.00      | sK7 = k1_xboole_0 ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3221,c_14]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3231,plain,
% 2.91/1.00      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.91/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3226,c_3221]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7323,plain,
% 2.91/1.00      ( sK7 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.91/1.00      inference(demodulation,[status(thm)],[c_3463,c_3231]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7335,plain,
% 2.91/1.00      ( sK7 = k1_xboole_0 ),
% 2.91/1.00      inference(equality_resolution_simp,[status(thm)],[c_7323]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_13,negated_conjecture,
% 2.91/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK7 ),
% 2.91/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7660,plain,
% 2.91/1.00      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
% 2.91/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.91/1.00      inference(demodulation,[status(thm)],[c_7335,c_13]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7661,plain,
% 2.91/1.00      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 2.91/1.00      inference(equality_resolution_simp,[status(thm)],[c_7660]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7663,plain,
% 2.91/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.91/1.00      inference(demodulation,[status(thm)],[c_7661,c_3448]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7664,plain,
% 2.91/1.00      ( $false ),
% 2.91/1.00      inference(equality_resolution_simp,[status(thm)],[c_7663]) ).
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  ------                               Statistics
% 2.91/1.00  
% 2.91/1.00  ------ General
% 2.91/1.00  
% 2.91/1.00  abstr_ref_over_cycles:                  0
% 2.91/1.00  abstr_ref_under_cycles:                 0
% 2.91/1.00  gc_basic_clause_elim:                   0
% 2.91/1.00  forced_gc_time:                         0
% 2.91/1.00  parsing_time:                           0.008
% 2.91/1.00  unif_index_cands_time:                  0.
% 2.91/1.00  unif_index_add_time:                    0.
% 2.91/1.00  orderings_time:                         0.
% 2.91/1.00  out_proof_time:                         0.008
% 2.91/1.00  total_time:                             0.223
% 2.91/1.00  num_of_symbols:                         45
% 2.91/1.00  num_of_terms:                           10052
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing
% 2.91/1.00  
% 2.91/1.00  num_of_splits:                          0
% 2.91/1.00  num_of_split_atoms:                     0
% 2.91/1.00  num_of_reused_defs:                     0
% 2.91/1.00  num_eq_ax_congr_red:                    36
% 2.91/1.00  num_of_sem_filtered_clauses:            1
% 2.91/1.00  num_of_subtypes:                        0
% 2.91/1.00  monotx_restored_types:                  0
% 2.91/1.00  sat_num_of_epr_types:                   0
% 2.91/1.00  sat_num_of_non_cyclic_types:            0
% 2.91/1.00  sat_guarded_non_collapsed_types:        0
% 2.91/1.00  num_pure_diseq_elim:                    0
% 2.91/1.00  simp_replaced_by:                       0
% 2.91/1.00  res_preprocessed:                       61
% 2.91/1.00  prep_upred:                             0
% 2.91/1.00  prep_unflattend:                        0
% 2.91/1.00  smt_new_axioms:                         0
% 2.91/1.00  pred_elim_cands:                        1
% 2.91/1.00  pred_elim:                              0
% 2.91/1.00  pred_elim_cl:                           0
% 2.91/1.00  pred_elim_cycles:                       1
% 2.91/1.00  merged_defs:                            6
% 2.91/1.00  merged_defs_ncl:                        0
% 2.91/1.00  bin_hyper_res:                          6
% 2.91/1.00  prep_cycles:                            3
% 2.91/1.00  pred_elim_time:                         0.
% 2.91/1.00  splitting_time:                         0.
% 2.91/1.00  sem_filter_time:                        0.
% 2.91/1.00  monotx_time:                            0.
% 2.91/1.00  subtype_inf_time:                       0.
% 2.91/1.00  
% 2.91/1.00  ------ Problem properties
% 2.91/1.00  
% 2.91/1.00  clauses:                                16
% 2.91/1.00  conjectures:                            3
% 2.91/1.00  epr:                                    0
% 2.91/1.00  horn:                                   10
% 2.91/1.00  ground:                                 3
% 2.91/1.00  unary:                                  1
% 2.91/1.00  binary:                                 7
% 2.91/1.00  lits:                                   41
% 2.91/1.00  lits_eq:                                19
% 2.91/1.00  fd_pure:                                0
% 2.91/1.00  fd_pseudo:                              0
% 2.91/1.00  fd_cond:                                0
% 2.91/1.00  fd_pseudo_cond:                         6
% 2.91/1.00  ac_symbols:                             0
% 2.91/1.00  
% 2.91/1.00  ------ Propositional Solver
% 2.91/1.00  
% 2.91/1.00  prop_solver_calls:                      25
% 2.91/1.00  prop_fast_solver_calls:                 816
% 2.91/1.00  smt_solver_calls:                       0
% 2.91/1.00  smt_fast_solver_calls:                  0
% 2.91/1.00  prop_num_of_clauses:                    2704
% 2.91/1.00  prop_preprocess_simplified:             5723
% 2.91/1.00  prop_fo_subsumed:                       162
% 2.91/1.00  prop_solver_time:                       0.
% 2.91/1.00  smt_solver_time:                        0.
% 2.91/1.00  smt_fast_solver_time:                   0.
% 2.91/1.00  prop_fast_solver_time:                  0.
% 2.91/1.00  prop_unsat_core_time:                   0.
% 2.91/1.00  
% 2.91/1.00  ------ QBF
% 2.91/1.00  
% 2.91/1.00  qbf_q_res:                              0
% 2.91/1.00  qbf_num_tautologies:                    0
% 2.91/1.00  qbf_prep_cycles:                        0
% 2.91/1.00  
% 2.91/1.00  ------ BMC1
% 2.91/1.00  
% 2.91/1.00  bmc1_current_bound:                     -1
% 2.91/1.00  bmc1_last_solved_bound:                 -1
% 2.91/1.00  bmc1_unsat_core_size:                   -1
% 2.91/1.00  bmc1_unsat_core_parents_size:           -1
% 2.91/1.00  bmc1_merge_next_fun:                    0
% 2.91/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation
% 2.91/1.00  
% 2.91/1.00  inst_num_of_clauses:                    666
% 2.91/1.00  inst_num_in_passive:                    225
% 2.91/1.00  inst_num_in_active:                     212
% 2.91/1.00  inst_num_in_unprocessed:                229
% 2.91/1.00  inst_num_of_loops:                      360
% 2.91/1.00  inst_num_of_learning_restarts:          0
% 2.91/1.00  inst_num_moves_active_passive:          145
% 2.91/1.00  inst_lit_activity:                      0
% 2.91/1.00  inst_lit_activity_moves:                0
% 2.91/1.00  inst_num_tautologies:                   0
% 2.91/1.00  inst_num_prop_implied:                  0
% 2.91/1.00  inst_num_existing_simplified:           0
% 2.91/1.00  inst_num_eq_res_simplified:             0
% 2.91/1.00  inst_num_child_elim:                    0
% 2.91/1.00  inst_num_of_dismatching_blockings:      191
% 2.91/1.00  inst_num_of_non_proper_insts:           438
% 2.91/1.00  inst_num_of_duplicates:                 0
% 2.91/1.00  inst_inst_num_from_inst_to_res:         0
% 2.91/1.00  inst_dismatching_checking_time:         0.
% 2.91/1.00  
% 2.91/1.00  ------ Resolution
% 2.91/1.00  
% 2.91/1.00  res_num_of_clauses:                     0
% 2.91/1.00  res_num_in_passive:                     0
% 2.91/1.00  res_num_in_active:                      0
% 2.91/1.00  res_num_of_loops:                       64
% 2.91/1.00  res_forward_subset_subsumed:            34
% 2.91/1.00  res_backward_subset_subsumed:           0
% 2.91/1.00  res_forward_subsumed:                   0
% 2.91/1.00  res_backward_subsumed:                  0
% 2.91/1.00  res_forward_subsumption_resolution:     0
% 2.91/1.00  res_backward_subsumption_resolution:    0
% 2.91/1.00  res_clause_to_clause_subsumption:       1164
% 2.91/1.00  res_orphan_elimination:                 0
% 2.91/1.00  res_tautology_del:                      54
% 2.91/1.00  res_num_eq_res_simplified:              0
% 2.91/1.00  res_num_sel_changes:                    0
% 2.91/1.00  res_moves_from_active_to_pass:          0
% 2.91/1.00  
% 2.91/1.00  ------ Superposition
% 2.91/1.00  
% 2.91/1.00  sup_time_total:                         0.
% 2.91/1.00  sup_time_generating:                    0.
% 2.91/1.00  sup_time_sim_full:                      0.
% 2.91/1.00  sup_time_sim_immed:                     0.
% 2.91/1.00  
% 2.91/1.00  sup_num_of_clauses:                     239
% 2.91/1.00  sup_num_in_active:                      25
% 2.91/1.00  sup_num_in_passive:                     214
% 2.91/1.00  sup_num_of_loops:                       70
% 2.91/1.00  sup_fw_superposition:                   441
% 2.91/1.00  sup_bw_superposition:                   221
% 2.91/1.00  sup_immediate_simplified:               262
% 2.91/1.00  sup_given_eliminated:                   18
% 2.91/1.00  comparisons_done:                       0
% 2.91/1.00  comparisons_avoided:                    16
% 2.91/1.00  
% 2.91/1.00  ------ Simplifications
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  sim_fw_subset_subsumed:                 23
% 2.91/1.00  sim_bw_subset_subsumed:                 7
% 2.91/1.00  sim_fw_subsumed:                        64
% 2.91/1.00  sim_bw_subsumed:                        0
% 2.91/1.00  sim_fw_subsumption_res:                 2
% 2.91/1.00  sim_bw_subsumption_res:                 0
% 2.91/1.00  sim_tautology_del:                      5
% 2.91/1.00  sim_eq_tautology_del:                   11
% 2.91/1.00  sim_eq_res_simp:                        2
% 2.91/1.00  sim_fw_demodulated:                     115
% 2.91/1.00  sim_bw_demodulated:                     67
% 2.91/1.00  sim_light_normalised:                   62
% 2.91/1.00  sim_joinable_taut:                      0
% 2.91/1.00  sim_joinable_simp:                      0
% 2.91/1.00  sim_ac_normalised:                      0
% 2.91/1.00  sim_smt_subsumption:                    0
% 2.91/1.00  
%------------------------------------------------------------------------------
