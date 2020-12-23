%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:59 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 405 expanded)
%              Number of clauses        :   42 ( 157 expanded)
%              Number of leaves         :   11 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          :  289 (1702 expanded)
%              Number of equality atoms :  157 ( 743 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,
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

fof(f25,plain,
    ( ( ( k1_xboole_0 != sK7
        & k1_xboole_0 != sK6 )
      | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).

fof(f41,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_500,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_173,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_tarski(X0) != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_174,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_489,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_778,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_489])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_493,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_764,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_493,c_489])).

cnf(c_2331,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_778,c_764])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_492,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1967,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_764])).

cnf(c_2334,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_778,c_1967])).

cnf(c_2343,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2331,c_2334])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_495,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1094,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_495])).

cnf(c_1127,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1094,c_489])).

cnf(c_1131,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(X1,sK6)) != iProver_top
    | r2_hidden(X2,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_493,c_1127])).

cnf(c_1268,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK6))) != iProver_top
    | r2_hidden(X3,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_493,c_1131])).

cnf(c_1442,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1445,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1442])).

cnf(c_1133,plain,
    ( sK6 = X0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(sK0(X0,sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_1127])).

cnf(c_1455,plain,
    ( sK6 = X0
    | sK6 = k1_xboole_0
    | sK7 = X1
    | sK7 = k1_xboole_0
    | r2_hidden(sK0(X0,sK6),X0) = iProver_top
    | r2_hidden(sK0(X1,sK7),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_1133])).

cnf(c_1508,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_1626,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1629,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_1644,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1268,c_1445,c_1508,c_1629])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1649,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1644,c_16])).

cnf(c_1654,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1649,c_1644])).

cnf(c_2505,plain,
    ( sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2343,c_1654])).

cnf(c_2509,plain,
    ( sK7 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2505])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2669,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2509,c_15])).

cnf(c_2670,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2669])).

cnf(c_2672,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2670,c_2331])).

cnf(c_2673,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2672])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.70/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.03  
% 2.70/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/1.03  
% 2.70/1.03  ------  iProver source info
% 2.70/1.03  
% 2.70/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.70/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/1.03  git: non_committed_changes: false
% 2.70/1.03  git: last_make_outside_of_git: false
% 2.70/1.03  
% 2.70/1.03  ------ 
% 2.70/1.03  
% 2.70/1.03  ------ Input Options
% 2.70/1.03  
% 2.70/1.03  --out_options                           all
% 2.70/1.03  --tptp_safe_out                         true
% 2.70/1.03  --problem_path                          ""
% 2.70/1.03  --include_path                          ""
% 2.70/1.03  --clausifier                            res/vclausify_rel
% 2.70/1.03  --clausifier_options                    --mode clausify
% 2.70/1.03  --stdin                                 false
% 2.70/1.03  --stats_out                             all
% 2.70/1.03  
% 2.70/1.03  ------ General Options
% 2.70/1.03  
% 2.70/1.03  --fof                                   false
% 2.70/1.03  --time_out_real                         305.
% 2.70/1.03  --time_out_virtual                      -1.
% 2.70/1.03  --symbol_type_check                     false
% 2.70/1.03  --clausify_out                          false
% 2.70/1.03  --sig_cnt_out                           false
% 2.70/1.03  --trig_cnt_out                          false
% 2.70/1.03  --trig_cnt_out_tolerance                1.
% 2.70/1.03  --trig_cnt_out_sk_spl                   false
% 2.70/1.03  --abstr_cl_out                          false
% 2.70/1.03  
% 2.70/1.03  ------ Global Options
% 2.70/1.03  
% 2.70/1.03  --schedule                              default
% 2.70/1.03  --add_important_lit                     false
% 2.70/1.03  --prop_solver_per_cl                    1000
% 2.70/1.03  --min_unsat_core                        false
% 2.70/1.03  --soft_assumptions                      false
% 2.70/1.03  --soft_lemma_size                       3
% 2.70/1.03  --prop_impl_unit_size                   0
% 2.70/1.03  --prop_impl_unit                        []
% 2.70/1.03  --share_sel_clauses                     true
% 2.70/1.03  --reset_solvers                         false
% 2.70/1.03  --bc_imp_inh                            [conj_cone]
% 2.70/1.03  --conj_cone_tolerance                   3.
% 2.70/1.03  --extra_neg_conj                        none
% 2.70/1.03  --large_theory_mode                     true
% 2.70/1.03  --prolific_symb_bound                   200
% 2.70/1.03  --lt_threshold                          2000
% 2.70/1.03  --clause_weak_htbl                      true
% 2.70/1.03  --gc_record_bc_elim                     false
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing Options
% 2.70/1.03  
% 2.70/1.03  --preprocessing_flag                    true
% 2.70/1.03  --time_out_prep_mult                    0.1
% 2.70/1.03  --splitting_mode                        input
% 2.70/1.03  --splitting_grd                         true
% 2.70/1.03  --splitting_cvd                         false
% 2.70/1.03  --splitting_cvd_svl                     false
% 2.70/1.03  --splitting_nvd                         32
% 2.70/1.03  --sub_typing                            true
% 2.70/1.03  --prep_gs_sim                           true
% 2.70/1.03  --prep_unflatten                        true
% 2.70/1.03  --prep_res_sim                          true
% 2.70/1.03  --prep_upred                            true
% 2.70/1.03  --prep_sem_filter                       exhaustive
% 2.70/1.03  --prep_sem_filter_out                   false
% 2.70/1.03  --pred_elim                             true
% 2.70/1.03  --res_sim_input                         true
% 2.70/1.03  --eq_ax_congr_red                       true
% 2.70/1.03  --pure_diseq_elim                       true
% 2.70/1.03  --brand_transform                       false
% 2.70/1.03  --non_eq_to_eq                          false
% 2.70/1.03  --prep_def_merge                        true
% 2.70/1.03  --prep_def_merge_prop_impl              false
% 2.70/1.03  --prep_def_merge_mbd                    true
% 2.70/1.03  --prep_def_merge_tr_red                 false
% 2.70/1.03  --prep_def_merge_tr_cl                  false
% 2.70/1.03  --smt_preprocessing                     true
% 2.70/1.03  --smt_ac_axioms                         fast
% 2.70/1.03  --preprocessed_out                      false
% 2.70/1.03  --preprocessed_stats                    false
% 2.70/1.03  
% 2.70/1.03  ------ Abstraction refinement Options
% 2.70/1.03  
% 2.70/1.03  --abstr_ref                             []
% 2.70/1.03  --abstr_ref_prep                        false
% 2.70/1.03  --abstr_ref_until_sat                   false
% 2.70/1.03  --abstr_ref_sig_restrict                funpre
% 2.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.03  --abstr_ref_under                       []
% 2.70/1.03  
% 2.70/1.03  ------ SAT Options
% 2.70/1.03  
% 2.70/1.03  --sat_mode                              false
% 2.70/1.03  --sat_fm_restart_options                ""
% 2.70/1.03  --sat_gr_def                            false
% 2.70/1.03  --sat_epr_types                         true
% 2.70/1.03  --sat_non_cyclic_types                  false
% 2.70/1.03  --sat_finite_models                     false
% 2.70/1.03  --sat_fm_lemmas                         false
% 2.70/1.03  --sat_fm_prep                           false
% 2.70/1.03  --sat_fm_uc_incr                        true
% 2.70/1.03  --sat_out_model                         small
% 2.70/1.03  --sat_out_clauses                       false
% 2.70/1.03  
% 2.70/1.03  ------ QBF Options
% 2.70/1.03  
% 2.70/1.03  --qbf_mode                              false
% 2.70/1.03  --qbf_elim_univ                         false
% 2.70/1.03  --qbf_dom_inst                          none
% 2.70/1.03  --qbf_dom_pre_inst                      false
% 2.70/1.03  --qbf_sk_in                             false
% 2.70/1.03  --qbf_pred_elim                         true
% 2.70/1.03  --qbf_split                             512
% 2.70/1.03  
% 2.70/1.03  ------ BMC1 Options
% 2.70/1.03  
% 2.70/1.03  --bmc1_incremental                      false
% 2.70/1.03  --bmc1_axioms                           reachable_all
% 2.70/1.03  --bmc1_min_bound                        0
% 2.70/1.03  --bmc1_max_bound                        -1
% 2.70/1.03  --bmc1_max_bound_default                -1
% 2.70/1.03  --bmc1_symbol_reachability              true
% 2.70/1.03  --bmc1_property_lemmas                  false
% 2.70/1.03  --bmc1_k_induction                      false
% 2.70/1.03  --bmc1_non_equiv_states                 false
% 2.70/1.03  --bmc1_deadlock                         false
% 2.70/1.03  --bmc1_ucm                              false
% 2.70/1.03  --bmc1_add_unsat_core                   none
% 2.70/1.03  --bmc1_unsat_core_children              false
% 2.70/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.03  --bmc1_out_stat                         full
% 2.70/1.03  --bmc1_ground_init                      false
% 2.70/1.03  --bmc1_pre_inst_next_state              false
% 2.70/1.03  --bmc1_pre_inst_state                   false
% 2.70/1.03  --bmc1_pre_inst_reach_state             false
% 2.70/1.03  --bmc1_out_unsat_core                   false
% 2.70/1.03  --bmc1_aig_witness_out                  false
% 2.70/1.03  --bmc1_verbose                          false
% 2.70/1.03  --bmc1_dump_clauses_tptp                false
% 2.70/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.03  --bmc1_dump_file                        -
% 2.70/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.03  --bmc1_ucm_extend_mode                  1
% 2.70/1.03  --bmc1_ucm_init_mode                    2
% 2.70/1.03  --bmc1_ucm_cone_mode                    none
% 2.70/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.03  --bmc1_ucm_relax_model                  4
% 2.70/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.03  --bmc1_ucm_layered_model                none
% 2.70/1.03  --bmc1_ucm_max_lemma_size               10
% 2.70/1.03  
% 2.70/1.03  ------ AIG Options
% 2.70/1.03  
% 2.70/1.03  --aig_mode                              false
% 2.70/1.03  
% 2.70/1.03  ------ Instantiation Options
% 2.70/1.03  
% 2.70/1.03  --instantiation_flag                    true
% 2.70/1.03  --inst_sos_flag                         false
% 2.70/1.03  --inst_sos_phase                        true
% 2.70/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel_side                     num_symb
% 2.70/1.03  --inst_solver_per_active                1400
% 2.70/1.03  --inst_solver_calls_frac                1.
% 2.70/1.03  --inst_passive_queue_type               priority_queues
% 2.70/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.03  --inst_passive_queues_freq              [25;2]
% 2.70/1.03  --inst_dismatching                      true
% 2.70/1.03  --inst_eager_unprocessed_to_passive     true
% 2.70/1.03  --inst_prop_sim_given                   true
% 2.70/1.03  --inst_prop_sim_new                     false
% 2.70/1.03  --inst_subs_new                         false
% 2.70/1.03  --inst_eq_res_simp                      false
% 2.70/1.03  --inst_subs_given                       false
% 2.70/1.03  --inst_orphan_elimination               true
% 2.70/1.03  --inst_learning_loop_flag               true
% 2.70/1.03  --inst_learning_start                   3000
% 2.70/1.03  --inst_learning_factor                  2
% 2.70/1.03  --inst_start_prop_sim_after_learn       3
% 2.70/1.03  --inst_sel_renew                        solver
% 2.70/1.03  --inst_lit_activity_flag                true
% 2.70/1.03  --inst_restr_to_given                   false
% 2.70/1.03  --inst_activity_threshold               500
% 2.70/1.03  --inst_out_proof                        true
% 2.70/1.03  
% 2.70/1.03  ------ Resolution Options
% 2.70/1.03  
% 2.70/1.03  --resolution_flag                       true
% 2.70/1.03  --res_lit_sel                           adaptive
% 2.70/1.03  --res_lit_sel_side                      none
% 2.70/1.03  --res_ordering                          kbo
% 2.70/1.03  --res_to_prop_solver                    active
% 2.70/1.03  --res_prop_simpl_new                    false
% 2.70/1.03  --res_prop_simpl_given                  true
% 2.70/1.03  --res_passive_queue_type                priority_queues
% 2.70/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.03  --res_passive_queues_freq               [15;5]
% 2.70/1.03  --res_forward_subs                      full
% 2.70/1.03  --res_backward_subs                     full
% 2.70/1.03  --res_forward_subs_resolution           true
% 2.70/1.03  --res_backward_subs_resolution          true
% 2.70/1.03  --res_orphan_elimination                true
% 2.70/1.03  --res_time_limit                        2.
% 2.70/1.03  --res_out_proof                         true
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Options
% 2.70/1.03  
% 2.70/1.03  --superposition_flag                    true
% 2.70/1.03  --sup_passive_queue_type                priority_queues
% 2.70/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.03  --demod_completeness_check              fast
% 2.70/1.03  --demod_use_ground                      true
% 2.70/1.03  --sup_to_prop_solver                    passive
% 2.70/1.03  --sup_prop_simpl_new                    true
% 2.70/1.03  --sup_prop_simpl_given                  true
% 2.70/1.03  --sup_fun_splitting                     false
% 2.70/1.03  --sup_smt_interval                      50000
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Simplification Setup
% 2.70/1.03  
% 2.70/1.03  --sup_indices_passive                   []
% 2.70/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_full_bw                           [BwDemod]
% 2.70/1.03  --sup_immed_triv                        [TrivRules]
% 2.70/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_immed_bw_main                     []
% 2.70/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  
% 2.70/1.03  ------ Combination Options
% 2.70/1.03  
% 2.70/1.03  --comb_res_mult                         3
% 2.70/1.03  --comb_sup_mult                         2
% 2.70/1.03  --comb_inst_mult                        10
% 2.70/1.03  
% 2.70/1.03  ------ Debug Options
% 2.70/1.03  
% 2.70/1.03  --dbg_backtrace                         false
% 2.70/1.03  --dbg_dump_prop_clauses                 false
% 2.70/1.03  --dbg_dump_prop_clauses_file            -
% 2.70/1.03  --dbg_out_stat                          false
% 2.70/1.03  ------ Parsing...
% 2.70/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/1.03  ------ Proving...
% 2.70/1.03  ------ Problem Properties 
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  clauses                                 16
% 2.70/1.03  conjectures                             3
% 2.70/1.03  EPR                                     1
% 2.70/1.03  Horn                                    11
% 2.70/1.03  unary                                   1
% 2.70/1.03  binary                                  7
% 2.70/1.03  lits                                    41
% 2.70/1.03  lits eq                                 16
% 2.70/1.03  fd_pure                                 0
% 2.70/1.03  fd_pseudo                               0
% 2.70/1.03  fd_cond                                 0
% 2.70/1.03  fd_pseudo_cond                          6
% 2.70/1.03  AC symbols                              0
% 2.70/1.03  
% 2.70/1.03  ------ Schedule dynamic 5 is on 
% 2.70/1.03  
% 2.70/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  ------ 
% 2.70/1.03  Current options:
% 2.70/1.03  ------ 
% 2.70/1.03  
% 2.70/1.03  ------ Input Options
% 2.70/1.03  
% 2.70/1.03  --out_options                           all
% 2.70/1.03  --tptp_safe_out                         true
% 2.70/1.03  --problem_path                          ""
% 2.70/1.03  --include_path                          ""
% 2.70/1.03  --clausifier                            res/vclausify_rel
% 2.70/1.03  --clausifier_options                    --mode clausify
% 2.70/1.03  --stdin                                 false
% 2.70/1.03  --stats_out                             all
% 2.70/1.03  
% 2.70/1.03  ------ General Options
% 2.70/1.03  
% 2.70/1.03  --fof                                   false
% 2.70/1.03  --time_out_real                         305.
% 2.70/1.03  --time_out_virtual                      -1.
% 2.70/1.03  --symbol_type_check                     false
% 2.70/1.03  --clausify_out                          false
% 2.70/1.03  --sig_cnt_out                           false
% 2.70/1.03  --trig_cnt_out                          false
% 2.70/1.03  --trig_cnt_out_tolerance                1.
% 2.70/1.03  --trig_cnt_out_sk_spl                   false
% 2.70/1.03  --abstr_cl_out                          false
% 2.70/1.03  
% 2.70/1.03  ------ Global Options
% 2.70/1.03  
% 2.70/1.03  --schedule                              default
% 2.70/1.03  --add_important_lit                     false
% 2.70/1.03  --prop_solver_per_cl                    1000
% 2.70/1.03  --min_unsat_core                        false
% 2.70/1.03  --soft_assumptions                      false
% 2.70/1.03  --soft_lemma_size                       3
% 2.70/1.03  --prop_impl_unit_size                   0
% 2.70/1.03  --prop_impl_unit                        []
% 2.70/1.03  --share_sel_clauses                     true
% 2.70/1.03  --reset_solvers                         false
% 2.70/1.03  --bc_imp_inh                            [conj_cone]
% 2.70/1.03  --conj_cone_tolerance                   3.
% 2.70/1.03  --extra_neg_conj                        none
% 2.70/1.03  --large_theory_mode                     true
% 2.70/1.03  --prolific_symb_bound                   200
% 2.70/1.03  --lt_threshold                          2000
% 2.70/1.03  --clause_weak_htbl                      true
% 2.70/1.03  --gc_record_bc_elim                     false
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing Options
% 2.70/1.03  
% 2.70/1.03  --preprocessing_flag                    true
% 2.70/1.03  --time_out_prep_mult                    0.1
% 2.70/1.03  --splitting_mode                        input
% 2.70/1.03  --splitting_grd                         true
% 2.70/1.03  --splitting_cvd                         false
% 2.70/1.03  --splitting_cvd_svl                     false
% 2.70/1.03  --splitting_nvd                         32
% 2.70/1.03  --sub_typing                            true
% 2.70/1.03  --prep_gs_sim                           true
% 2.70/1.03  --prep_unflatten                        true
% 2.70/1.03  --prep_res_sim                          true
% 2.70/1.03  --prep_upred                            true
% 2.70/1.03  --prep_sem_filter                       exhaustive
% 2.70/1.03  --prep_sem_filter_out                   false
% 2.70/1.03  --pred_elim                             true
% 2.70/1.03  --res_sim_input                         true
% 2.70/1.03  --eq_ax_congr_red                       true
% 2.70/1.03  --pure_diseq_elim                       true
% 2.70/1.03  --brand_transform                       false
% 2.70/1.03  --non_eq_to_eq                          false
% 2.70/1.03  --prep_def_merge                        true
% 2.70/1.03  --prep_def_merge_prop_impl              false
% 2.70/1.03  --prep_def_merge_mbd                    true
% 2.70/1.03  --prep_def_merge_tr_red                 false
% 2.70/1.03  --prep_def_merge_tr_cl                  false
% 2.70/1.03  --smt_preprocessing                     true
% 2.70/1.03  --smt_ac_axioms                         fast
% 2.70/1.03  --preprocessed_out                      false
% 2.70/1.03  --preprocessed_stats                    false
% 2.70/1.03  
% 2.70/1.03  ------ Abstraction refinement Options
% 2.70/1.03  
% 2.70/1.03  --abstr_ref                             []
% 2.70/1.03  --abstr_ref_prep                        false
% 2.70/1.03  --abstr_ref_until_sat                   false
% 2.70/1.03  --abstr_ref_sig_restrict                funpre
% 2.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.03  --abstr_ref_under                       []
% 2.70/1.03  
% 2.70/1.03  ------ SAT Options
% 2.70/1.03  
% 2.70/1.03  --sat_mode                              false
% 2.70/1.03  --sat_fm_restart_options                ""
% 2.70/1.03  --sat_gr_def                            false
% 2.70/1.03  --sat_epr_types                         true
% 2.70/1.03  --sat_non_cyclic_types                  false
% 2.70/1.03  --sat_finite_models                     false
% 2.70/1.03  --sat_fm_lemmas                         false
% 2.70/1.03  --sat_fm_prep                           false
% 2.70/1.03  --sat_fm_uc_incr                        true
% 2.70/1.03  --sat_out_model                         small
% 2.70/1.03  --sat_out_clauses                       false
% 2.70/1.03  
% 2.70/1.03  ------ QBF Options
% 2.70/1.03  
% 2.70/1.03  --qbf_mode                              false
% 2.70/1.03  --qbf_elim_univ                         false
% 2.70/1.03  --qbf_dom_inst                          none
% 2.70/1.03  --qbf_dom_pre_inst                      false
% 2.70/1.03  --qbf_sk_in                             false
% 2.70/1.03  --qbf_pred_elim                         true
% 2.70/1.03  --qbf_split                             512
% 2.70/1.03  
% 2.70/1.03  ------ BMC1 Options
% 2.70/1.03  
% 2.70/1.03  --bmc1_incremental                      false
% 2.70/1.03  --bmc1_axioms                           reachable_all
% 2.70/1.03  --bmc1_min_bound                        0
% 2.70/1.03  --bmc1_max_bound                        -1
% 2.70/1.03  --bmc1_max_bound_default                -1
% 2.70/1.03  --bmc1_symbol_reachability              true
% 2.70/1.03  --bmc1_property_lemmas                  false
% 2.70/1.03  --bmc1_k_induction                      false
% 2.70/1.03  --bmc1_non_equiv_states                 false
% 2.70/1.03  --bmc1_deadlock                         false
% 2.70/1.03  --bmc1_ucm                              false
% 2.70/1.03  --bmc1_add_unsat_core                   none
% 2.70/1.03  --bmc1_unsat_core_children              false
% 2.70/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.03  --bmc1_out_stat                         full
% 2.70/1.03  --bmc1_ground_init                      false
% 2.70/1.03  --bmc1_pre_inst_next_state              false
% 2.70/1.03  --bmc1_pre_inst_state                   false
% 2.70/1.03  --bmc1_pre_inst_reach_state             false
% 2.70/1.03  --bmc1_out_unsat_core                   false
% 2.70/1.03  --bmc1_aig_witness_out                  false
% 2.70/1.03  --bmc1_verbose                          false
% 2.70/1.03  --bmc1_dump_clauses_tptp                false
% 2.70/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.03  --bmc1_dump_file                        -
% 2.70/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.03  --bmc1_ucm_extend_mode                  1
% 2.70/1.03  --bmc1_ucm_init_mode                    2
% 2.70/1.03  --bmc1_ucm_cone_mode                    none
% 2.70/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.03  --bmc1_ucm_relax_model                  4
% 2.70/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.03  --bmc1_ucm_layered_model                none
% 2.70/1.03  --bmc1_ucm_max_lemma_size               10
% 2.70/1.03  
% 2.70/1.03  ------ AIG Options
% 2.70/1.03  
% 2.70/1.03  --aig_mode                              false
% 2.70/1.03  
% 2.70/1.03  ------ Instantiation Options
% 2.70/1.03  
% 2.70/1.03  --instantiation_flag                    true
% 2.70/1.03  --inst_sos_flag                         false
% 2.70/1.03  --inst_sos_phase                        true
% 2.70/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel_side                     none
% 2.70/1.03  --inst_solver_per_active                1400
% 2.70/1.03  --inst_solver_calls_frac                1.
% 2.70/1.03  --inst_passive_queue_type               priority_queues
% 2.70/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.03  --inst_passive_queues_freq              [25;2]
% 2.70/1.03  --inst_dismatching                      true
% 2.70/1.03  --inst_eager_unprocessed_to_passive     true
% 2.70/1.03  --inst_prop_sim_given                   true
% 2.70/1.03  --inst_prop_sim_new                     false
% 2.70/1.03  --inst_subs_new                         false
% 2.70/1.03  --inst_eq_res_simp                      false
% 2.70/1.03  --inst_subs_given                       false
% 2.70/1.03  --inst_orphan_elimination               true
% 2.70/1.03  --inst_learning_loop_flag               true
% 2.70/1.03  --inst_learning_start                   3000
% 2.70/1.03  --inst_learning_factor                  2
% 2.70/1.03  --inst_start_prop_sim_after_learn       3
% 2.70/1.03  --inst_sel_renew                        solver
% 2.70/1.03  --inst_lit_activity_flag                true
% 2.70/1.03  --inst_restr_to_given                   false
% 2.70/1.03  --inst_activity_threshold               500
% 2.70/1.03  --inst_out_proof                        true
% 2.70/1.03  
% 2.70/1.03  ------ Resolution Options
% 2.70/1.03  
% 2.70/1.03  --resolution_flag                       false
% 2.70/1.03  --res_lit_sel                           adaptive
% 2.70/1.03  --res_lit_sel_side                      none
% 2.70/1.03  --res_ordering                          kbo
% 2.70/1.03  --res_to_prop_solver                    active
% 2.70/1.03  --res_prop_simpl_new                    false
% 2.70/1.03  --res_prop_simpl_given                  true
% 2.70/1.03  --res_passive_queue_type                priority_queues
% 2.70/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.03  --res_passive_queues_freq               [15;5]
% 2.70/1.03  --res_forward_subs                      full
% 2.70/1.03  --res_backward_subs                     full
% 2.70/1.03  --res_forward_subs_resolution           true
% 2.70/1.03  --res_backward_subs_resolution          true
% 2.70/1.03  --res_orphan_elimination                true
% 2.70/1.03  --res_time_limit                        2.
% 2.70/1.03  --res_out_proof                         true
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Options
% 2.70/1.03  
% 2.70/1.03  --superposition_flag                    true
% 2.70/1.03  --sup_passive_queue_type                priority_queues
% 2.70/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.03  --demod_completeness_check              fast
% 2.70/1.03  --demod_use_ground                      true
% 2.70/1.03  --sup_to_prop_solver                    passive
% 2.70/1.03  --sup_prop_simpl_new                    true
% 2.70/1.03  --sup_prop_simpl_given                  true
% 2.70/1.03  --sup_fun_splitting                     false
% 2.70/1.03  --sup_smt_interval                      50000
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Simplification Setup
% 2.70/1.03  
% 2.70/1.03  --sup_indices_passive                   []
% 2.70/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_full_bw                           [BwDemod]
% 2.70/1.03  --sup_immed_triv                        [TrivRules]
% 2.70/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_immed_bw_main                     []
% 2.70/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  
% 2.70/1.03  ------ Combination Options
% 2.70/1.03  
% 2.70/1.03  --comb_res_mult                         3
% 2.70/1.03  --comb_sup_mult                         2
% 2.70/1.03  --comb_inst_mult                        10
% 2.70/1.03  
% 2.70/1.03  ------ Debug Options
% 2.70/1.03  
% 2.70/1.03  --dbg_backtrace                         false
% 2.70/1.03  --dbg_dump_prop_clauses                 false
% 2.70/1.03  --dbg_dump_prop_clauses_file            -
% 2.70/1.03  --dbg_out_stat                          false
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  ------ Proving...
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  % SZS status Theorem for theBenchmark.p
% 2.70/1.03  
% 2.70/1.03   Resolution empty clause
% 2.70/1.03  
% 2.70/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/1.03  
% 2.70/1.03  fof(f1,axiom,(
% 2.70/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f8,plain,(
% 2.70/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.70/1.03    inference(ennf_transformation,[],[f1])).
% 2.70/1.03  
% 2.70/1.03  fof(f11,plain,(
% 2.70/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.70/1.03    inference(nnf_transformation,[],[f8])).
% 2.70/1.03  
% 2.70/1.03  fof(f12,plain,(
% 2.70/1.03    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f13,plain,(
% 2.70/1.03    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 2.70/1.03  
% 2.70/1.03  fof(f26,plain,(
% 2.70/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f13])).
% 2.70/1.03  
% 2.70/1.03  fof(f2,axiom,(
% 2.70/1.03    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f28,plain,(
% 2.70/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f2])).
% 2.70/1.03  
% 2.70/1.03  fof(f4,axiom,(
% 2.70/1.03    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 2.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f9,plain,(
% 2.70/1.03    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.70/1.03    inference(ennf_transformation,[],[f4])).
% 2.70/1.03  
% 2.70/1.03  fof(f37,plain,(
% 2.70/1.03    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f9])).
% 2.70/1.03  
% 2.70/1.03  fof(f3,axiom,(
% 2.70/1.03    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f14,plain,(
% 2.70/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.70/1.03    inference(nnf_transformation,[],[f3])).
% 2.70/1.03  
% 2.70/1.03  fof(f15,plain,(
% 2.70/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.70/1.03    inference(rectify,[],[f14])).
% 2.70/1.03  
% 2.70/1.03  fof(f18,plain,(
% 2.70/1.03    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f17,plain,(
% 2.70/1.03    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f16,plain,(
% 2.70/1.03    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f19,plain,(
% 2.70/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 2.70/1.03  
% 2.70/1.03  fof(f30,plain,(
% 2.70/1.03    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.70/1.03    inference(cnf_transformation,[],[f19])).
% 2.70/1.03  
% 2.70/1.03  fof(f47,plain,(
% 2.70/1.03    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.70/1.03    inference(equality_resolution,[],[f30])).
% 2.70/1.03  
% 2.70/1.03  fof(f29,plain,(
% 2.70/1.03    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.70/1.03    inference(cnf_transformation,[],[f19])).
% 2.70/1.03  
% 2.70/1.03  fof(f48,plain,(
% 2.70/1.03    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.70/1.03    inference(equality_resolution,[],[f29])).
% 2.70/1.03  
% 2.70/1.03  fof(f6,conjecture,(
% 2.70/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f7,negated_conjecture,(
% 2.70/1.03    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.70/1.03    inference(negated_conjecture,[],[f6])).
% 2.70/1.03  
% 2.70/1.03  fof(f10,plain,(
% 2.70/1.03    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.70/1.03    inference(ennf_transformation,[],[f7])).
% 2.70/1.03  
% 2.70/1.03  fof(f22,plain,(
% 2.70/1.03    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.70/1.03    inference(nnf_transformation,[],[f10])).
% 2.70/1.03  
% 2.70/1.03  fof(f23,plain,(
% 2.70/1.03    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.70/1.03    inference(flattening,[],[f22])).
% 2.70/1.03  
% 2.70/1.03  fof(f24,plain,(
% 2.70/1.03    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f25,plain,(
% 2.70/1.03    ((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7))),
% 2.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).
% 2.70/1.03  
% 2.70/1.03  fof(f41,plain,(
% 2.70/1.03    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 2.70/1.03    inference(cnf_transformation,[],[f25])).
% 2.70/1.03  
% 2.70/1.03  fof(f5,axiom,(
% 2.70/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f20,plain,(
% 2.70/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.70/1.03    inference(nnf_transformation,[],[f5])).
% 2.70/1.03  
% 2.70/1.03  fof(f21,plain,(
% 2.70/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.70/1.03    inference(flattening,[],[f20])).
% 2.70/1.03  
% 2.70/1.03  fof(f40,plain,(
% 2.70/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f21])).
% 2.70/1.03  
% 2.70/1.03  fof(f42,plain,(
% 2.70/1.03    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 2.70/1.03    inference(cnf_transformation,[],[f25])).
% 2.70/1.03  
% 2.70/1.03  fof(f43,plain,(
% 2.70/1.03    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 2.70/1.03    inference(cnf_transformation,[],[f25])).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1,plain,
% 2.70/1.03      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.70/1.03      inference(cnf_transformation,[],[f26]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_500,plain,
% 2.70/1.03      ( X0 = X1
% 2.70/1.03      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.70/1.03      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2,plain,
% 2.70/1.03      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.70/1.03      inference(cnf_transformation,[],[f28]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_11,plain,
% 2.70/1.03      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.70/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_173,plain,
% 2.70/1.03      ( ~ r2_hidden(X0,X1) | k1_tarski(X0) != X2 | k1_xboole_0 != X1 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_174,plain,
% 2.70/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.70/1.03      inference(unflattening,[status(thm)],[c_173]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_489,plain,
% 2.70/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_778,plain,
% 2.70/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_500,c_489]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_9,plain,
% 2.70/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 2.70/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_493,plain,
% 2.70/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.70/1.03      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_764,plain,
% 2.70/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_493,c_489]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2331,plain,
% 2.70/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_778,c_764]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_10,plain,
% 2.70/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 2.70/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_492,plain,
% 2.70/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.70/1.03      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1967,plain,
% 2.70/1.03      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)) != iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_492,c_764]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2334,plain,
% 2.70/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_778,c_1967]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2343,plain,
% 2.70/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.70/1.03      inference(demodulation,[status(thm)],[c_2331,c_2334]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_17,negated_conjecture,
% 2.70/1.03      ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
% 2.70/1.03      | k1_xboole_0 = sK6
% 2.70/1.03      | k1_xboole_0 = sK7 ),
% 2.70/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_12,plain,
% 2.70/1.03      ( ~ r2_hidden(X0,X1)
% 2.70/1.03      | ~ r2_hidden(X2,X3)
% 2.70/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.70/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_495,plain,
% 2.70/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.70/1.03      | r2_hidden(X2,X3) != iProver_top
% 2.70/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1094,plain,
% 2.70/1.03      ( sK6 = k1_xboole_0
% 2.70/1.03      | sK7 = k1_xboole_0
% 2.70/1.03      | r2_hidden(X0,sK6) != iProver_top
% 2.70/1.03      | r2_hidden(X1,sK7) != iProver_top
% 2.70/1.03      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_17,c_495]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1127,plain,
% 2.70/1.03      ( sK6 = k1_xboole_0
% 2.70/1.03      | sK7 = k1_xboole_0
% 2.70/1.03      | r2_hidden(X0,sK6) != iProver_top
% 2.70/1.03      | r2_hidden(X1,sK7) != iProver_top ),
% 2.70/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1094,c_489]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1131,plain,
% 2.70/1.03      ( sK6 = k1_xboole_0
% 2.70/1.03      | sK7 = k1_xboole_0
% 2.70/1.03      | r2_hidden(X0,k2_zfmisc_1(X1,sK6)) != iProver_top
% 2.70/1.03      | r2_hidden(X2,sK7) != iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_493,c_1127]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1268,plain,
% 2.70/1.03      ( sK6 = k1_xboole_0
% 2.70/1.03      | sK7 = k1_xboole_0
% 2.70/1.03      | r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK6))) != iProver_top
% 2.70/1.03      | r2_hidden(X3,sK7) != iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_493,c_1131]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1442,plain,
% 2.70/1.03      ( ~ r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_174]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1445,plain,
% 2.70/1.03      ( r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_1442]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1133,plain,
% 2.70/1.03      ( sK6 = X0
% 2.70/1.03      | sK6 = k1_xboole_0
% 2.70/1.03      | sK7 = k1_xboole_0
% 2.70/1.03      | r2_hidden(X1,sK7) != iProver_top
% 2.70/1.03      | r2_hidden(sK0(X0,sK6),X0) = iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_500,c_1127]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1455,plain,
% 2.70/1.03      ( sK6 = X0
% 2.70/1.03      | sK6 = k1_xboole_0
% 2.70/1.03      | sK7 = X1
% 2.70/1.03      | sK7 = k1_xboole_0
% 2.70/1.03      | r2_hidden(sK0(X0,sK6),X0) = iProver_top
% 2.70/1.03      | r2_hidden(sK0(X1,sK7),X1) = iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_500,c_1133]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1508,plain,
% 2.70/1.03      ( sK6 = k1_xboole_0
% 2.70/1.03      | sK7 = k1_xboole_0
% 2.70/1.03      | r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) = iProver_top
% 2.70/1.03      | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_1455]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1626,plain,
% 2.70/1.03      ( ~ r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_174]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1629,plain,
% 2.70/1.03      ( r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1644,plain,
% 2.70/1.03      ( sK6 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_1268,c_1445,c_1508,c_1629]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_16,negated_conjecture,
% 2.70/1.03      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK6 ),
% 2.70/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1649,plain,
% 2.70/1.03      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
% 2.70/1.03      | sK6 != k1_xboole_0
% 2.70/1.03      | sK7 = k1_xboole_0 ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_1644,c_16]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1654,plain,
% 2.70/1.03      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.70/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1649,c_1644]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2505,plain,
% 2.70/1.03      ( sK7 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.70/1.03      inference(demodulation,[status(thm)],[c_2343,c_1654]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2509,plain,
% 2.70/1.03      ( sK7 = k1_xboole_0 ),
% 2.70/1.03      inference(equality_resolution_simp,[status(thm)],[c_2505]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_15,negated_conjecture,
% 2.70/1.03      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK7 ),
% 2.70/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2669,plain,
% 2.70/1.03      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
% 2.70/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.70/1.03      inference(demodulation,[status(thm)],[c_2509,c_15]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2670,plain,
% 2.70/1.03      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 2.70/1.03      inference(equality_resolution_simp,[status(thm)],[c_2669]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2672,plain,
% 2.70/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 2.70/1.03      inference(demodulation,[status(thm)],[c_2670,c_2331]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2673,plain,
% 2.70/1.03      ( $false ),
% 2.70/1.03      inference(equality_resolution_simp,[status(thm)],[c_2672]) ).
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/1.03  
% 2.70/1.03  ------                               Statistics
% 2.70/1.03  
% 2.70/1.03  ------ General
% 2.70/1.03  
% 2.70/1.03  abstr_ref_over_cycles:                  0
% 2.70/1.03  abstr_ref_under_cycles:                 0
% 2.70/1.03  gc_basic_clause_elim:                   0
% 2.70/1.03  forced_gc_time:                         0
% 2.70/1.03  parsing_time:                           0.008
% 2.70/1.03  unif_index_cands_time:                  0.
% 2.70/1.03  unif_index_add_time:                    0.
% 2.70/1.03  orderings_time:                         0.
% 2.70/1.03  out_proof_time:                         0.01
% 2.70/1.03  total_time:                             0.116
% 2.70/1.03  num_of_symbols:                         45
% 2.70/1.03  num_of_terms:                           2799
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing
% 2.70/1.03  
% 2.70/1.03  num_of_splits:                          0
% 2.70/1.03  num_of_split_atoms:                     0
% 2.70/1.03  num_of_reused_defs:                     0
% 2.70/1.03  num_eq_ax_congr_red:                    52
% 2.70/1.03  num_of_sem_filtered_clauses:            1
% 2.70/1.03  num_of_subtypes:                        0
% 2.70/1.03  monotx_restored_types:                  0
% 2.70/1.03  sat_num_of_epr_types:                   0
% 2.70/1.03  sat_num_of_non_cyclic_types:            0
% 2.70/1.03  sat_guarded_non_collapsed_types:        0
% 2.70/1.03  num_pure_diseq_elim:                    0
% 2.70/1.03  simp_replaced_by:                       0
% 2.70/1.03  res_preprocessed:                       76
% 2.70/1.03  prep_upred:                             0
% 2.70/1.03  prep_unflattend:                        2
% 2.70/1.03  smt_new_axioms:                         0
% 2.70/1.03  pred_elim_cands:                        1
% 2.70/1.03  pred_elim:                              1
% 2.70/1.03  pred_elim_cl:                           1
% 2.70/1.03  pred_elim_cycles:                       3
% 2.70/1.03  merged_defs:                            0
% 2.70/1.03  merged_defs_ncl:                        0
% 2.70/1.03  bin_hyper_res:                          0
% 2.70/1.03  prep_cycles:                            4
% 2.70/1.03  pred_elim_time:                         0.
% 2.70/1.03  splitting_time:                         0.
% 2.70/1.03  sem_filter_time:                        0.
% 2.70/1.03  monotx_time:                            0.
% 2.70/1.03  subtype_inf_time:                       0.
% 2.70/1.03  
% 2.70/1.03  ------ Problem properties
% 2.70/1.03  
% 2.70/1.03  clauses:                                16
% 2.70/1.03  conjectures:                            3
% 2.70/1.03  epr:                                    1
% 2.70/1.03  horn:                                   11
% 2.70/1.03  ground:                                 3
% 2.70/1.03  unary:                                  1
% 2.70/1.03  binary:                                 7
% 2.70/1.03  lits:                                   41
% 2.70/1.03  lits_eq:                                16
% 2.70/1.03  fd_pure:                                0
% 2.70/1.03  fd_pseudo:                              0
% 2.70/1.03  fd_cond:                                0
% 2.70/1.03  fd_pseudo_cond:                         6
% 2.70/1.03  ac_symbols:                             0
% 2.70/1.03  
% 2.70/1.03  ------ Propositional Solver
% 2.70/1.03  
% 2.70/1.03  prop_solver_calls:                      28
% 2.70/1.03  prop_fast_solver_calls:                 576
% 2.70/1.03  smt_solver_calls:                       0
% 2.70/1.03  smt_fast_solver_calls:                  0
% 2.70/1.03  prop_num_of_clauses:                    919
% 2.70/1.03  prop_preprocess_simplified:             3160
% 2.70/1.03  prop_fo_subsumed:                       42
% 2.70/1.03  prop_solver_time:                       0.
% 2.70/1.03  smt_solver_time:                        0.
% 2.70/1.03  smt_fast_solver_time:                   0.
% 2.70/1.03  prop_fast_solver_time:                  0.
% 2.70/1.03  prop_unsat_core_time:                   0.
% 2.70/1.03  
% 2.70/1.03  ------ QBF
% 2.70/1.03  
% 2.70/1.03  qbf_q_res:                              0
% 2.70/1.03  qbf_num_tautologies:                    0
% 2.70/1.03  qbf_prep_cycles:                        0
% 2.70/1.03  
% 2.70/1.03  ------ BMC1
% 2.70/1.03  
% 2.70/1.03  bmc1_current_bound:                     -1
% 2.70/1.03  bmc1_last_solved_bound:                 -1
% 2.70/1.03  bmc1_unsat_core_size:                   -1
% 2.70/1.03  bmc1_unsat_core_parents_size:           -1
% 2.70/1.03  bmc1_merge_next_fun:                    0
% 2.70/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.70/1.03  
% 2.70/1.03  ------ Instantiation
% 2.70/1.03  
% 2.70/1.03  inst_num_of_clauses:                    227
% 2.70/1.03  inst_num_in_passive:                    116
% 2.70/1.03  inst_num_in_active:                     101
% 2.70/1.03  inst_num_in_unprocessed:                10
% 2.70/1.03  inst_num_of_loops:                      170
% 2.70/1.03  inst_num_of_learning_restarts:          0
% 2.70/1.03  inst_num_moves_active_passive:          65
% 2.70/1.03  inst_lit_activity:                      0
% 2.70/1.03  inst_lit_activity_moves:                0
% 2.70/1.03  inst_num_tautologies:                   0
% 2.70/1.03  inst_num_prop_implied:                  0
% 2.70/1.03  inst_num_existing_simplified:           0
% 2.70/1.03  inst_num_eq_res_simplified:             0
% 2.70/1.03  inst_num_child_elim:                    0
% 2.70/1.03  inst_num_of_dismatching_blockings:      0
% 2.70/1.03  inst_num_of_non_proper_insts:           118
% 2.70/1.03  inst_num_of_duplicates:                 0
% 2.70/1.03  inst_inst_num_from_inst_to_res:         0
% 2.70/1.03  inst_dismatching_checking_time:         0.
% 2.70/1.03  
% 2.70/1.03  ------ Resolution
% 2.70/1.03  
% 2.70/1.03  res_num_of_clauses:                     0
% 2.70/1.03  res_num_in_passive:                     0
% 2.70/1.03  res_num_in_active:                      0
% 2.70/1.03  res_num_of_loops:                       80
% 2.70/1.03  res_forward_subset_subsumed:            4
% 2.70/1.03  res_backward_subset_subsumed:           0
% 2.70/1.03  res_forward_subsumed:                   0
% 2.70/1.03  res_backward_subsumed:                  0
% 2.70/1.03  res_forward_subsumption_resolution:     0
% 2.70/1.03  res_backward_subsumption_resolution:    0
% 2.70/1.03  res_clause_to_clause_subsumption:       244
% 2.70/1.03  res_orphan_elimination:                 0
% 2.70/1.03  res_tautology_del:                      20
% 2.70/1.03  res_num_eq_res_simplified:              0
% 2.70/1.03  res_num_sel_changes:                    0
% 2.70/1.03  res_moves_from_active_to_pass:          0
% 2.70/1.03  
% 2.70/1.03  ------ Superposition
% 2.70/1.03  
% 2.70/1.03  sup_time_total:                         0.
% 2.70/1.03  sup_time_generating:                    0.
% 2.70/1.03  sup_time_sim_full:                      0.
% 2.70/1.03  sup_time_sim_immed:                     0.
% 2.70/1.03  
% 2.70/1.03  sup_num_of_clauses:                     86
% 2.70/1.03  sup_num_in_active:                      18
% 2.70/1.03  sup_num_in_passive:                     68
% 2.70/1.03  sup_num_of_loops:                       33
% 2.70/1.03  sup_fw_superposition:                   84
% 2.70/1.03  sup_bw_superposition:                   69
% 2.70/1.03  sup_immediate_simplified:               35
% 2.70/1.03  sup_given_eliminated:                   0
% 2.70/1.03  comparisons_done:                       0
% 2.70/1.03  comparisons_avoided:                    8
% 2.70/1.03  
% 2.70/1.03  ------ Simplifications
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  sim_fw_subset_subsumed:                 14
% 2.70/1.03  sim_bw_subset_subsumed:                 6
% 2.70/1.03  sim_fw_subsumed:                        16
% 2.70/1.03  sim_bw_subsumed:                        0
% 2.70/1.03  sim_fw_subsumption_res:                 2
% 2.70/1.03  sim_bw_subsumption_res:                 0
% 2.70/1.03  sim_tautology_del:                      7
% 2.70/1.03  sim_eq_tautology_del:                   4
% 2.70/1.03  sim_eq_res_simp:                        2
% 2.70/1.03  sim_fw_demodulated:                     5
% 2.70/1.03  sim_bw_demodulated:                     15
% 2.70/1.03  sim_light_normalised:                   2
% 2.70/1.03  sim_joinable_taut:                      0
% 2.70/1.03  sim_joinable_simp:                      0
% 2.70/1.03  sim_ac_normalised:                      0
% 2.70/1.03  sim_smt_subsumption:                    0
% 2.70/1.03  
%------------------------------------------------------------------------------
