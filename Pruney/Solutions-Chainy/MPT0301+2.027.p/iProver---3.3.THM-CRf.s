%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:59 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   94 (2447 expanded)
%              Number of clauses        :   48 ( 665 expanded)
%              Number of leaves         :   13 ( 662 expanded)
%              Depth                    :   25
%              Number of atoms          :  288 (11658 expanded)
%              Number of equality atoms :  169 (4541 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

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
     => ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
        & r2_hidden(sK4(X0,X1,X8),X1)
        & r2_hidden(sK3(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
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
              ( k4_tarski(X4,X5) != sK0(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK0(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK0(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = sK0(X0,X1,X2)
              & r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
                & r2_hidden(sK4(X0,X1,X8),X1)
                & r2_hidden(sK3(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f18,f17,f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f60,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f53])).

fof(f33,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK6
          & k1_xboole_0 != sK5 )
        | k1_xboole_0 != k2_zfmisc_1(sK5,sK6) )
      & ( k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | k1_xboole_0 = k2_zfmisc_1(sK5,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ( k1_xboole_0 != sK6
        & k1_xboole_0 != sK5 )
      | k1_xboole_0 != k2_zfmisc_1(sK5,sK6) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = k2_zfmisc_1(sK5,sK6) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f26])).

fof(f47,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,
    ( k1_xboole_0 != sK5
    | k1_xboole_0 != k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_499,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_186,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_187,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_491,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_720,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_187,c_491])).

cnf(c_1388,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_720])).

cnf(c_1377,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_720])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_495,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_496,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_787,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_495,c_720])).

cnf(c_849,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_787])).

cnf(c_907,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_495,c_849])).

cnf(c_5044,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1377,c_907])).

cnf(c_1078,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3),X4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_495,c_907])).

cnf(c_5054,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3),X4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1377,c_1078])).

cnf(c_5077,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5044,c_5054])).

cnf(c_6291,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1388,c_5077])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK5,sK6)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_498,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1292,plain,
    ( sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_498])).

cnf(c_1577,plain,
    ( sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_720])).

cnf(c_6296,plain,
    ( sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6291,c_1577])).

cnf(c_6618,plain,
    ( sK5 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6291,c_6296])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK5,sK6)
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6663,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK6) != k1_xboole_0
    | sK5 != k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6618,c_17])).

cnf(c_6665,plain,
    ( sK5 != k1_xboole_0
    | sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6663,c_5077])).

cnf(c_6666,plain,
    ( sK5 != k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6665])).

cnf(c_6667,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6666,c_6618])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK5,sK6)
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6671,plain,
    ( k2_zfmisc_1(sK5,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6667,c_16])).

cnf(c_6672,plain,
    ( k2_zfmisc_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6671])).

cnf(c_1077,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(k1_xboole_0,X3)),X4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_907])).

cnf(c_6314,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6291,c_1077])).

cnf(c_850,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_495,c_787])).

cnf(c_957,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_850])).

cnf(c_5045,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)),X3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1377,c_957])).

cnf(c_5079,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5077,c_5045])).

cnf(c_5085,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5079,c_5077])).

cnf(c_6344,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6314,c_5077,c_5085])).

cnf(c_6673,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6672,c_6344])).

cnf(c_6674,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6673])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.09  % Command    : iproveropt_run.sh %d %s
% 0.08/0.27  % Computer   : n016.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 20:47:49 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  % Running in FOF mode
% 3.74/0.89  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/0.89  
% 3.74/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.89  
% 3.74/0.89  ------  iProver source info
% 3.74/0.89  
% 3.74/0.89  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.89  git: non_committed_changes: false
% 3.74/0.89  git: last_make_outside_of_git: false
% 3.74/0.89  
% 3.74/0.89  ------ 
% 3.74/0.89  
% 3.74/0.89  ------ Input Options
% 3.74/0.89  
% 3.74/0.89  --out_options                           all
% 3.74/0.89  --tptp_safe_out                         true
% 3.74/0.89  --problem_path                          ""
% 3.74/0.89  --include_path                          ""
% 3.74/0.89  --clausifier                            res/vclausify_rel
% 3.74/0.89  --clausifier_options                    ""
% 3.74/0.89  --stdin                                 false
% 3.74/0.89  --stats_out                             all
% 3.74/0.89  
% 3.74/0.89  ------ General Options
% 3.74/0.89  
% 3.74/0.89  --fof                                   false
% 3.74/0.89  --time_out_real                         305.
% 3.74/0.89  --time_out_virtual                      -1.
% 3.74/0.89  --symbol_type_check                     false
% 3.74/0.89  --clausify_out                          false
% 3.74/0.89  --sig_cnt_out                           false
% 3.74/0.89  --trig_cnt_out                          false
% 3.74/0.89  --trig_cnt_out_tolerance                1.
% 3.74/0.89  --trig_cnt_out_sk_spl                   false
% 3.74/0.89  --abstr_cl_out                          false
% 3.74/0.89  
% 3.74/0.89  ------ Global Options
% 3.74/0.89  
% 3.74/0.89  --schedule                              default
% 3.74/0.89  --add_important_lit                     false
% 3.74/0.89  --prop_solver_per_cl                    1000
% 3.74/0.89  --min_unsat_core                        false
% 3.74/0.89  --soft_assumptions                      false
% 3.74/0.89  --soft_lemma_size                       3
% 3.74/0.89  --prop_impl_unit_size                   0
% 3.74/0.89  --prop_impl_unit                        []
% 3.74/0.89  --share_sel_clauses                     true
% 3.74/0.89  --reset_solvers                         false
% 3.74/0.89  --bc_imp_inh                            [conj_cone]
% 3.74/0.89  --conj_cone_tolerance                   3.
% 3.74/0.89  --extra_neg_conj                        none
% 3.74/0.89  --large_theory_mode                     true
% 3.74/0.89  --prolific_symb_bound                   200
% 3.74/0.89  --lt_threshold                          2000
% 3.74/0.89  --clause_weak_htbl                      true
% 3.74/0.89  --gc_record_bc_elim                     false
% 3.74/0.89  
% 3.74/0.89  ------ Preprocessing Options
% 3.74/0.89  
% 3.74/0.89  --preprocessing_flag                    true
% 3.74/0.89  --time_out_prep_mult                    0.1
% 3.74/0.89  --splitting_mode                        input
% 3.74/0.89  --splitting_grd                         true
% 3.74/0.89  --splitting_cvd                         false
% 3.74/0.89  --splitting_cvd_svl                     false
% 3.74/0.89  --splitting_nvd                         32
% 3.74/0.89  --sub_typing                            true
% 3.74/0.89  --prep_gs_sim                           true
% 3.74/0.89  --prep_unflatten                        true
% 3.74/0.89  --prep_res_sim                          true
% 3.74/0.89  --prep_upred                            true
% 3.74/0.89  --prep_sem_filter                       exhaustive
% 3.74/0.89  --prep_sem_filter_out                   false
% 3.74/0.89  --pred_elim                             true
% 3.74/0.89  --res_sim_input                         true
% 3.74/0.89  --eq_ax_congr_red                       true
% 3.74/0.89  --pure_diseq_elim                       true
% 3.74/0.89  --brand_transform                       false
% 3.74/0.89  --non_eq_to_eq                          false
% 3.74/0.89  --prep_def_merge                        true
% 3.74/0.89  --prep_def_merge_prop_impl              false
% 3.74/0.89  --prep_def_merge_mbd                    true
% 3.74/0.89  --prep_def_merge_tr_red                 false
% 3.74/0.89  --prep_def_merge_tr_cl                  false
% 3.74/0.89  --smt_preprocessing                     true
% 3.74/0.89  --smt_ac_axioms                         fast
% 3.74/0.89  --preprocessed_out                      false
% 3.74/0.89  --preprocessed_stats                    false
% 3.74/0.89  
% 3.74/0.89  ------ Abstraction refinement Options
% 3.74/0.89  
% 3.74/0.89  --abstr_ref                             []
% 3.74/0.89  --abstr_ref_prep                        false
% 3.74/0.89  --abstr_ref_until_sat                   false
% 3.74/0.89  --abstr_ref_sig_restrict                funpre
% 3.74/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/0.89  --abstr_ref_under                       []
% 3.74/0.89  
% 3.74/0.89  ------ SAT Options
% 3.74/0.89  
% 3.74/0.89  --sat_mode                              false
% 3.74/0.89  --sat_fm_restart_options                ""
% 3.74/0.89  --sat_gr_def                            false
% 3.74/0.89  --sat_epr_types                         true
% 3.74/0.89  --sat_non_cyclic_types                  false
% 3.74/0.89  --sat_finite_models                     false
% 3.74/0.89  --sat_fm_lemmas                         false
% 3.74/0.89  --sat_fm_prep                           false
% 3.74/0.89  --sat_fm_uc_incr                        true
% 3.74/0.89  --sat_out_model                         small
% 3.74/0.89  --sat_out_clauses                       false
% 3.74/0.89  
% 3.74/0.89  ------ QBF Options
% 3.74/0.89  
% 3.74/0.89  --qbf_mode                              false
% 3.74/0.89  --qbf_elim_univ                         false
% 3.74/0.89  --qbf_dom_inst                          none
% 3.74/0.89  --qbf_dom_pre_inst                      false
% 3.74/0.89  --qbf_sk_in                             false
% 3.74/0.89  --qbf_pred_elim                         true
% 3.74/0.89  --qbf_split                             512
% 3.74/0.89  
% 3.74/0.89  ------ BMC1 Options
% 3.74/0.89  
% 3.74/0.89  --bmc1_incremental                      false
% 3.74/0.89  --bmc1_axioms                           reachable_all
% 3.74/0.89  --bmc1_min_bound                        0
% 3.74/0.89  --bmc1_max_bound                        -1
% 3.74/0.89  --bmc1_max_bound_default                -1
% 3.74/0.89  --bmc1_symbol_reachability              true
% 3.74/0.89  --bmc1_property_lemmas                  false
% 3.74/0.89  --bmc1_k_induction                      false
% 3.74/0.89  --bmc1_non_equiv_states                 false
% 3.74/0.89  --bmc1_deadlock                         false
% 3.74/0.89  --bmc1_ucm                              false
% 3.74/0.89  --bmc1_add_unsat_core                   none
% 3.74/0.89  --bmc1_unsat_core_children              false
% 3.74/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/0.89  --bmc1_out_stat                         full
% 3.74/0.89  --bmc1_ground_init                      false
% 3.74/0.89  --bmc1_pre_inst_next_state              false
% 3.74/0.89  --bmc1_pre_inst_state                   false
% 3.74/0.89  --bmc1_pre_inst_reach_state             false
% 3.74/0.89  --bmc1_out_unsat_core                   false
% 3.74/0.89  --bmc1_aig_witness_out                  false
% 3.74/0.89  --bmc1_verbose                          false
% 3.74/0.89  --bmc1_dump_clauses_tptp                false
% 3.74/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.74/0.89  --bmc1_dump_file                        -
% 3.74/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.74/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.74/0.89  --bmc1_ucm_extend_mode                  1
% 3.74/0.89  --bmc1_ucm_init_mode                    2
% 3.74/0.89  --bmc1_ucm_cone_mode                    none
% 3.74/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.74/0.89  --bmc1_ucm_relax_model                  4
% 3.74/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.74/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/0.89  --bmc1_ucm_layered_model                none
% 3.74/0.89  --bmc1_ucm_max_lemma_size               10
% 3.74/0.89  
% 3.74/0.89  ------ AIG Options
% 3.74/0.89  
% 3.74/0.89  --aig_mode                              false
% 3.74/0.89  
% 3.74/0.89  ------ Instantiation Options
% 3.74/0.89  
% 3.74/0.89  --instantiation_flag                    true
% 3.74/0.89  --inst_sos_flag                         true
% 3.74/0.89  --inst_sos_phase                        true
% 3.74/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/0.89  --inst_lit_sel_side                     num_symb
% 3.74/0.89  --inst_solver_per_active                1400
% 3.74/0.89  --inst_solver_calls_frac                1.
% 3.74/0.89  --inst_passive_queue_type               priority_queues
% 3.74/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/0.89  --inst_passive_queues_freq              [25;2]
% 3.74/0.89  --inst_dismatching                      true
% 3.74/0.89  --inst_eager_unprocessed_to_passive     true
% 3.74/0.89  --inst_prop_sim_given                   true
% 3.74/0.89  --inst_prop_sim_new                     false
% 3.74/0.89  --inst_subs_new                         false
% 3.74/0.89  --inst_eq_res_simp                      false
% 3.74/0.89  --inst_subs_given                       false
% 3.74/0.89  --inst_orphan_elimination               true
% 3.74/0.89  --inst_learning_loop_flag               true
% 3.74/0.89  --inst_learning_start                   3000
% 3.74/0.89  --inst_learning_factor                  2
% 3.74/0.89  --inst_start_prop_sim_after_learn       3
% 3.74/0.89  --inst_sel_renew                        solver
% 3.74/0.89  --inst_lit_activity_flag                true
% 3.74/0.89  --inst_restr_to_given                   false
% 3.74/0.89  --inst_activity_threshold               500
% 3.74/0.89  --inst_out_proof                        true
% 3.74/0.89  
% 3.74/0.89  ------ Resolution Options
% 3.74/0.89  
% 3.74/0.89  --resolution_flag                       true
% 3.74/0.89  --res_lit_sel                           adaptive
% 3.74/0.89  --res_lit_sel_side                      none
% 3.74/0.89  --res_ordering                          kbo
% 3.74/0.89  --res_to_prop_solver                    active
% 3.74/0.89  --res_prop_simpl_new                    false
% 3.74/0.89  --res_prop_simpl_given                  true
% 3.74/0.89  --res_passive_queue_type                priority_queues
% 3.74/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/0.89  --res_passive_queues_freq               [15;5]
% 3.74/0.89  --res_forward_subs                      full
% 3.74/0.89  --res_backward_subs                     full
% 3.74/0.89  --res_forward_subs_resolution           true
% 3.74/0.89  --res_backward_subs_resolution          true
% 3.74/0.89  --res_orphan_elimination                true
% 3.74/0.89  --res_time_limit                        2.
% 3.74/0.89  --res_out_proof                         true
% 3.74/0.89  
% 3.74/0.89  ------ Superposition Options
% 3.74/0.89  
% 3.74/0.89  --superposition_flag                    true
% 3.74/0.89  --sup_passive_queue_type                priority_queues
% 3.74/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.74/0.89  --demod_completeness_check              fast
% 3.74/0.89  --demod_use_ground                      true
% 3.74/0.89  --sup_to_prop_solver                    passive
% 3.74/0.89  --sup_prop_simpl_new                    true
% 3.74/0.89  --sup_prop_simpl_given                  true
% 3.74/0.89  --sup_fun_splitting                     true
% 3.74/0.89  --sup_smt_interval                      50000
% 3.74/0.89  
% 3.74/0.89  ------ Superposition Simplification Setup
% 3.74/0.89  
% 3.74/0.89  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/0.89  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/0.89  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/0.89  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/0.89  --sup_immed_triv                        [TrivRules]
% 3.74/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.89  --sup_immed_bw_main                     []
% 3.74/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.89  --sup_input_bw                          []
% 3.74/0.89  
% 3.74/0.89  ------ Combination Options
% 3.74/0.89  
% 3.74/0.89  --comb_res_mult                         3
% 3.74/0.89  --comb_sup_mult                         2
% 3.74/0.89  --comb_inst_mult                        10
% 3.74/0.89  
% 3.74/0.89  ------ Debug Options
% 3.74/0.89  
% 3.74/0.89  --dbg_backtrace                         false
% 3.74/0.89  --dbg_dump_prop_clauses                 false
% 3.74/0.89  --dbg_dump_prop_clauses_file            -
% 3.74/0.89  --dbg_out_stat                          false
% 3.74/0.89  ------ Parsing...
% 3.74/0.89  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.89  
% 3.74/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.74/0.89  
% 3.74/0.89  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.89  
% 3.74/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.89  ------ Proving...
% 3.74/0.89  ------ Problem Properties 
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  clauses                                 17
% 3.74/0.89  conjectures                             3
% 3.74/0.89  EPR                                     0
% 3.74/0.89  Horn                                    12
% 3.74/0.89  unary                                   2
% 3.74/0.89  binary                                  8
% 3.74/0.89  lits                                    41
% 3.74/0.89  lits eq                                 16
% 3.74/0.89  fd_pure                                 0
% 3.74/0.89  fd_pseudo                               0
% 3.74/0.89  fd_cond                                 0
% 3.74/0.89  fd_pseudo_cond                          5
% 3.74/0.89  AC symbols                              0
% 3.74/0.89  
% 3.74/0.89  ------ Schedule dynamic 5 is on 
% 3.74/0.89  
% 3.74/0.89  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  ------ 
% 3.74/0.89  Current options:
% 3.74/0.89  ------ 
% 3.74/0.89  
% 3.74/0.89  ------ Input Options
% 3.74/0.89  
% 3.74/0.89  --out_options                           all
% 3.74/0.89  --tptp_safe_out                         true
% 3.74/0.89  --problem_path                          ""
% 3.74/0.89  --include_path                          ""
% 3.74/0.89  --clausifier                            res/vclausify_rel
% 3.74/0.89  --clausifier_options                    ""
% 3.74/0.89  --stdin                                 false
% 3.74/0.89  --stats_out                             all
% 3.74/0.89  
% 3.74/0.89  ------ General Options
% 3.74/0.89  
% 3.74/0.89  --fof                                   false
% 3.74/0.89  --time_out_real                         305.
% 3.74/0.89  --time_out_virtual                      -1.
% 3.74/0.89  --symbol_type_check                     false
% 3.74/0.89  --clausify_out                          false
% 3.74/0.89  --sig_cnt_out                           false
% 3.74/0.89  --trig_cnt_out                          false
% 3.74/0.89  --trig_cnt_out_tolerance                1.
% 3.74/0.89  --trig_cnt_out_sk_spl                   false
% 3.74/0.89  --abstr_cl_out                          false
% 3.74/0.89  
% 3.74/0.89  ------ Global Options
% 3.74/0.89  
% 3.74/0.89  --schedule                              default
% 3.74/0.89  --add_important_lit                     false
% 3.74/0.89  --prop_solver_per_cl                    1000
% 3.74/0.89  --min_unsat_core                        false
% 3.74/0.89  --soft_assumptions                      false
% 3.74/0.89  --soft_lemma_size                       3
% 3.74/0.89  --prop_impl_unit_size                   0
% 3.74/0.89  --prop_impl_unit                        []
% 3.74/0.89  --share_sel_clauses                     true
% 3.74/0.89  --reset_solvers                         false
% 3.74/0.89  --bc_imp_inh                            [conj_cone]
% 3.74/0.89  --conj_cone_tolerance                   3.
% 3.74/0.89  --extra_neg_conj                        none
% 3.74/0.89  --large_theory_mode                     true
% 3.74/0.89  --prolific_symb_bound                   200
% 3.74/0.89  --lt_threshold                          2000
% 3.74/0.89  --clause_weak_htbl                      true
% 3.74/0.89  --gc_record_bc_elim                     false
% 3.74/0.89  
% 3.74/0.89  ------ Preprocessing Options
% 3.74/0.89  
% 3.74/0.89  --preprocessing_flag                    true
% 3.74/0.89  --time_out_prep_mult                    0.1
% 3.74/0.89  --splitting_mode                        input
% 3.74/0.89  --splitting_grd                         true
% 3.74/0.89  --splitting_cvd                         false
% 3.74/0.89  --splitting_cvd_svl                     false
% 3.74/0.89  --splitting_nvd                         32
% 3.74/0.89  --sub_typing                            true
% 3.74/0.89  --prep_gs_sim                           true
% 3.74/0.89  --prep_unflatten                        true
% 3.74/0.89  --prep_res_sim                          true
% 3.74/0.89  --prep_upred                            true
% 3.74/0.89  --prep_sem_filter                       exhaustive
% 3.74/0.89  --prep_sem_filter_out                   false
% 3.74/0.89  --pred_elim                             true
% 3.74/0.89  --res_sim_input                         true
% 3.74/0.89  --eq_ax_congr_red                       true
% 3.74/0.89  --pure_diseq_elim                       true
% 3.74/0.89  --brand_transform                       false
% 3.74/0.89  --non_eq_to_eq                          false
% 3.74/0.89  --prep_def_merge                        true
% 3.74/0.89  --prep_def_merge_prop_impl              false
% 3.74/0.89  --prep_def_merge_mbd                    true
% 3.74/0.89  --prep_def_merge_tr_red                 false
% 3.74/0.89  --prep_def_merge_tr_cl                  false
% 3.74/0.89  --smt_preprocessing                     true
% 3.74/0.89  --smt_ac_axioms                         fast
% 3.74/0.89  --preprocessed_out                      false
% 3.74/0.89  --preprocessed_stats                    false
% 3.74/0.89  
% 3.74/0.89  ------ Abstraction refinement Options
% 3.74/0.89  
% 3.74/0.89  --abstr_ref                             []
% 3.74/0.89  --abstr_ref_prep                        false
% 3.74/0.89  --abstr_ref_until_sat                   false
% 3.74/0.89  --abstr_ref_sig_restrict                funpre
% 3.74/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/0.89  --abstr_ref_under                       []
% 3.74/0.89  
% 3.74/0.89  ------ SAT Options
% 3.74/0.89  
% 3.74/0.89  --sat_mode                              false
% 3.74/0.89  --sat_fm_restart_options                ""
% 3.74/0.89  --sat_gr_def                            false
% 3.74/0.89  --sat_epr_types                         true
% 3.74/0.89  --sat_non_cyclic_types                  false
% 3.74/0.89  --sat_finite_models                     false
% 3.74/0.89  --sat_fm_lemmas                         false
% 3.74/0.89  --sat_fm_prep                           false
% 3.74/0.89  --sat_fm_uc_incr                        true
% 3.74/0.89  --sat_out_model                         small
% 3.74/0.89  --sat_out_clauses                       false
% 3.74/0.89  
% 3.74/0.89  ------ QBF Options
% 3.74/0.89  
% 3.74/0.89  --qbf_mode                              false
% 3.74/0.89  --qbf_elim_univ                         false
% 3.74/0.89  --qbf_dom_inst                          none
% 3.74/0.89  --qbf_dom_pre_inst                      false
% 3.74/0.89  --qbf_sk_in                             false
% 3.74/0.89  --qbf_pred_elim                         true
% 3.74/0.89  --qbf_split                             512
% 3.74/0.89  
% 3.74/0.89  ------ BMC1 Options
% 3.74/0.89  
% 3.74/0.89  --bmc1_incremental                      false
% 3.74/0.89  --bmc1_axioms                           reachable_all
% 3.74/0.89  --bmc1_min_bound                        0
% 3.74/0.89  --bmc1_max_bound                        -1
% 3.74/0.89  --bmc1_max_bound_default                -1
% 3.74/0.89  --bmc1_symbol_reachability              true
% 3.74/0.89  --bmc1_property_lemmas                  false
% 3.74/0.89  --bmc1_k_induction                      false
% 3.74/0.89  --bmc1_non_equiv_states                 false
% 3.74/0.89  --bmc1_deadlock                         false
% 3.74/0.89  --bmc1_ucm                              false
% 3.74/0.89  --bmc1_add_unsat_core                   none
% 3.74/0.89  --bmc1_unsat_core_children              false
% 3.74/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/0.89  --bmc1_out_stat                         full
% 3.74/0.89  --bmc1_ground_init                      false
% 3.74/0.89  --bmc1_pre_inst_next_state              false
% 3.74/0.89  --bmc1_pre_inst_state                   false
% 3.74/0.89  --bmc1_pre_inst_reach_state             false
% 3.74/0.89  --bmc1_out_unsat_core                   false
% 3.74/0.89  --bmc1_aig_witness_out                  false
% 3.74/0.89  --bmc1_verbose                          false
% 3.74/0.89  --bmc1_dump_clauses_tptp                false
% 3.74/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.74/0.89  --bmc1_dump_file                        -
% 3.74/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.74/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.74/0.89  --bmc1_ucm_extend_mode                  1
% 3.74/0.89  --bmc1_ucm_init_mode                    2
% 3.74/0.89  --bmc1_ucm_cone_mode                    none
% 3.74/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.74/0.89  --bmc1_ucm_relax_model                  4
% 3.74/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.74/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/0.89  --bmc1_ucm_layered_model                none
% 3.74/0.89  --bmc1_ucm_max_lemma_size               10
% 3.74/0.89  
% 3.74/0.89  ------ AIG Options
% 3.74/0.89  
% 3.74/0.89  --aig_mode                              false
% 3.74/0.89  
% 3.74/0.89  ------ Instantiation Options
% 3.74/0.89  
% 3.74/0.89  --instantiation_flag                    true
% 3.74/0.89  --inst_sos_flag                         true
% 3.74/0.89  --inst_sos_phase                        true
% 3.74/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/0.89  --inst_lit_sel_side                     none
% 3.74/0.89  --inst_solver_per_active                1400
% 3.74/0.89  --inst_solver_calls_frac                1.
% 3.74/0.89  --inst_passive_queue_type               priority_queues
% 3.74/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/0.89  --inst_passive_queues_freq              [25;2]
% 3.74/0.89  --inst_dismatching                      true
% 3.74/0.89  --inst_eager_unprocessed_to_passive     true
% 3.74/0.89  --inst_prop_sim_given                   true
% 3.74/0.89  --inst_prop_sim_new                     false
% 3.74/0.89  --inst_subs_new                         false
% 3.74/0.89  --inst_eq_res_simp                      false
% 3.74/0.89  --inst_subs_given                       false
% 3.74/0.89  --inst_orphan_elimination               true
% 3.74/0.89  --inst_learning_loop_flag               true
% 3.74/0.89  --inst_learning_start                   3000
% 3.74/0.89  --inst_learning_factor                  2
% 3.74/0.89  --inst_start_prop_sim_after_learn       3
% 3.74/0.89  --inst_sel_renew                        solver
% 3.74/0.89  --inst_lit_activity_flag                true
% 3.74/0.89  --inst_restr_to_given                   false
% 3.74/0.89  --inst_activity_threshold               500
% 3.74/0.89  --inst_out_proof                        true
% 3.74/0.89  
% 3.74/0.89  ------ Resolution Options
% 3.74/0.89  
% 3.74/0.89  --resolution_flag                       false
% 3.74/0.89  --res_lit_sel                           adaptive
% 3.74/0.89  --res_lit_sel_side                      none
% 3.74/0.89  --res_ordering                          kbo
% 3.74/0.89  --res_to_prop_solver                    active
% 3.74/0.89  --res_prop_simpl_new                    false
% 3.74/0.89  --res_prop_simpl_given                  true
% 3.74/0.89  --res_passive_queue_type                priority_queues
% 3.74/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/0.89  --res_passive_queues_freq               [15;5]
% 3.74/0.89  --res_forward_subs                      full
% 3.74/0.89  --res_backward_subs                     full
% 3.74/0.89  --res_forward_subs_resolution           true
% 3.74/0.89  --res_backward_subs_resolution          true
% 3.74/0.89  --res_orphan_elimination                true
% 3.74/0.89  --res_time_limit                        2.
% 3.74/0.89  --res_out_proof                         true
% 3.74/0.89  
% 3.74/0.89  ------ Superposition Options
% 3.74/0.89  
% 3.74/0.89  --superposition_flag                    true
% 3.74/0.89  --sup_passive_queue_type                priority_queues
% 3.74/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.74/0.89  --demod_completeness_check              fast
% 3.74/0.89  --demod_use_ground                      true
% 3.74/0.89  --sup_to_prop_solver                    passive
% 3.74/0.89  --sup_prop_simpl_new                    true
% 3.74/0.89  --sup_prop_simpl_given                  true
% 3.74/0.89  --sup_fun_splitting                     true
% 3.74/0.89  --sup_smt_interval                      50000
% 3.74/0.89  
% 3.74/0.89  ------ Superposition Simplification Setup
% 3.74/0.89  
% 3.74/0.89  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/0.89  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/0.89  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/0.89  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/0.89  --sup_immed_triv                        [TrivRules]
% 3.74/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.89  --sup_immed_bw_main                     []
% 3.74/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.89  --sup_input_bw                          []
% 3.74/0.89  
% 3.74/0.89  ------ Combination Options
% 3.74/0.89  
% 3.74/0.89  --comb_res_mult                         3
% 3.74/0.89  --comb_sup_mult                         2
% 3.74/0.89  --comb_inst_mult                        10
% 3.74/0.89  
% 3.74/0.89  ------ Debug Options
% 3.74/0.89  
% 3.74/0.89  --dbg_backtrace                         false
% 3.74/0.89  --dbg_dump_prop_clauses                 false
% 3.74/0.89  --dbg_dump_prop_clauses_file            -
% 3.74/0.89  --dbg_out_stat                          false
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  ------ Proving...
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  % SZS status Theorem for theBenchmark.p
% 3.74/0.89  
% 3.74/0.89   Resolution empty clause
% 3.74/0.89  
% 3.74/0.89  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.89  
% 3.74/0.89  fof(f6,axiom,(
% 3.74/0.89    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f14,plain,(
% 3.74/0.89    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.74/0.89    inference(nnf_transformation,[],[f6])).
% 3.74/0.89  
% 3.74/0.89  fof(f15,plain,(
% 3.74/0.89    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.74/0.89    inference(rectify,[],[f14])).
% 3.74/0.89  
% 3.74/0.89  fof(f18,plain,(
% 3.74/0.89    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8 & r2_hidden(sK4(X0,X1,X8),X1) & r2_hidden(sK3(X0,X1,X8),X0)))),
% 3.74/0.89    introduced(choice_axiom,[])).
% 3.74/0.89  
% 3.74/0.89  fof(f17,plain,(
% 3.74/0.89    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)))) )),
% 3.74/0.89    introduced(choice_axiom,[])).
% 3.74/0.89  
% 3.74/0.89  fof(f16,plain,(
% 3.74/0.89    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK0(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK0(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.74/0.89    introduced(choice_axiom,[])).
% 3.74/0.89  
% 3.74/0.89  fof(f19,plain,(
% 3.74/0.89    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK0(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = sK0(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8 & r2_hidden(sK4(X0,X1,X8),X1) & r2_hidden(sK3(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.74/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f18,f17,f16])).
% 3.74/0.89  
% 3.74/0.89  fof(f37,plain,(
% 3.74/0.89    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.74/0.89    inference(cnf_transformation,[],[f19])).
% 3.74/0.89  
% 3.74/0.89  fof(f1,axiom,(
% 3.74/0.89    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f11,plain,(
% 3.74/0.89    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 3.74/0.89    inference(unused_predicate_definition_removal,[],[f1])).
% 3.74/0.89  
% 3.74/0.89  fof(f12,plain,(
% 3.74/0.89    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 3.74/0.89    inference(ennf_transformation,[],[f11])).
% 3.74/0.89  
% 3.74/0.89  fof(f28,plain,(
% 3.74/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.74/0.89    inference(cnf_transformation,[],[f12])).
% 3.74/0.89  
% 3.74/0.89  fof(f2,axiom,(
% 3.74/0.89    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f29,plain,(
% 3.74/0.89    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.74/0.89    inference(cnf_transformation,[],[f2])).
% 3.74/0.89  
% 3.74/0.89  fof(f8,axiom,(
% 3.74/0.89    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f22,plain,(
% 3.74/0.89    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.74/0.89    inference(nnf_transformation,[],[f8])).
% 3.74/0.89  
% 3.74/0.89  fof(f23,plain,(
% 3.74/0.89    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.74/0.89    inference(flattening,[],[f22])).
% 3.74/0.89  
% 3.74/0.89  fof(f45,plain,(
% 3.74/0.89    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.74/0.89    inference(cnf_transformation,[],[f23])).
% 3.74/0.89  
% 3.74/0.89  fof(f3,axiom,(
% 3.74/0.89    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f30,plain,(
% 3.74/0.89    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.74/0.89    inference(cnf_transformation,[],[f3])).
% 3.74/0.89  
% 3.74/0.89  fof(f4,axiom,(
% 3.74/0.89    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f31,plain,(
% 3.74/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.74/0.89    inference(cnf_transformation,[],[f4])).
% 3.74/0.89  
% 3.74/0.89  fof(f5,axiom,(
% 3.74/0.89    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f32,plain,(
% 3.74/0.89    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.74/0.89    inference(cnf_transformation,[],[f5])).
% 3.74/0.89  
% 3.74/0.89  fof(f50,plain,(
% 3.74/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.74/0.89    inference(definition_unfolding,[],[f31,f32])).
% 3.74/0.89  
% 3.74/0.89  fof(f51,plain,(
% 3.74/0.89    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.74/0.89    inference(definition_unfolding,[],[f30,f50])).
% 3.74/0.89  
% 3.74/0.89  fof(f53,plain,(
% 3.74/0.89    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.74/0.89    inference(definition_unfolding,[],[f45,f51])).
% 3.74/0.89  
% 3.74/0.89  fof(f60,plain,(
% 3.74/0.89    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.74/0.89    inference(equality_resolution,[],[f53])).
% 3.74/0.89  
% 3.74/0.89  fof(f33,plain,(
% 3.74/0.89    ( ! [X2,X0,X8,X1] : (r2_hidden(sK3(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.74/0.89    inference(cnf_transformation,[],[f19])).
% 3.74/0.89  
% 3.74/0.89  fof(f59,plain,(
% 3.74/0.89    ( ! [X0,X8,X1] : (r2_hidden(sK3(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.74/0.89    inference(equality_resolution,[],[f33])).
% 3.74/0.89  
% 3.74/0.89  fof(f34,plain,(
% 3.74/0.89    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.74/0.89    inference(cnf_transformation,[],[f19])).
% 3.74/0.89  
% 3.74/0.89  fof(f58,plain,(
% 3.74/0.89    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.74/0.89    inference(equality_resolution,[],[f34])).
% 3.74/0.89  
% 3.74/0.89  fof(f9,conjecture,(
% 3.74/0.89    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f10,negated_conjecture,(
% 3.74/0.89    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.74/0.89    inference(negated_conjecture,[],[f9])).
% 3.74/0.89  
% 3.74/0.89  fof(f13,plain,(
% 3.74/0.89    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.74/0.89    inference(ennf_transformation,[],[f10])).
% 3.74/0.89  
% 3.74/0.89  fof(f24,plain,(
% 3.74/0.89    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.74/0.89    inference(nnf_transformation,[],[f13])).
% 3.74/0.89  
% 3.74/0.89  fof(f25,plain,(
% 3.74/0.89    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.74/0.89    inference(flattening,[],[f24])).
% 3.74/0.89  
% 3.74/0.89  fof(f26,plain,(
% 3.74/0.89    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK6 & k1_xboole_0 != sK5) | k1_xboole_0 != k2_zfmisc_1(sK5,sK6)) & (k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK5,sK6)))),
% 3.74/0.89    introduced(choice_axiom,[])).
% 3.74/0.89  
% 3.74/0.89  fof(f27,plain,(
% 3.74/0.89    ((k1_xboole_0 != sK6 & k1_xboole_0 != sK5) | k1_xboole_0 != k2_zfmisc_1(sK5,sK6)) & (k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK5,sK6))),
% 3.74/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f26])).
% 3.74/0.89  
% 3.74/0.89  fof(f47,plain,(
% 3.74/0.89    k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK5,sK6)),
% 3.74/0.89    inference(cnf_transformation,[],[f27])).
% 3.74/0.89  
% 3.74/0.89  fof(f7,axiom,(
% 3.74/0.89    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.74/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.89  
% 3.74/0.89  fof(f20,plain,(
% 3.74/0.89    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.74/0.89    inference(nnf_transformation,[],[f7])).
% 3.74/0.89  
% 3.74/0.89  fof(f21,plain,(
% 3.74/0.89    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.74/0.89    inference(flattening,[],[f20])).
% 3.74/0.89  
% 3.74/0.89  fof(f43,plain,(
% 3.74/0.89    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.74/0.89    inference(cnf_transformation,[],[f21])).
% 3.74/0.89  
% 3.74/0.89  fof(f48,plain,(
% 3.74/0.89    k1_xboole_0 != sK5 | k1_xboole_0 != k2_zfmisc_1(sK5,sK6)),
% 3.74/0.89    inference(cnf_transformation,[],[f27])).
% 3.74/0.89  
% 3.74/0.89  fof(f49,plain,(
% 3.74/0.89    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK5,sK6)),
% 3.74/0.89    inference(cnf_transformation,[],[f27])).
% 3.74/0.89  
% 3.74/0.89  cnf(c_5,plain,
% 3.74/0.89      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.74/0.89      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.74/0.89      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.74/0.89      inference(cnf_transformation,[],[f37]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_499,plain,
% 3.74/0.89      ( k2_zfmisc_1(X0,X1) = X2
% 3.74/0.89      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 3.74/0.89      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.74/0.89      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_0,plain,
% 3.74/0.89      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.74/0.89      inference(cnf_transformation,[],[f28]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_1,plain,
% 3.74/0.89      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.74/0.89      inference(cnf_transformation,[],[f29]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_186,plain,
% 3.74/0.89      ( X0 != X1
% 3.74/0.89      | k4_xboole_0(X0,X2) != X3
% 3.74/0.89      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 3.74/0.89      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_187,plain,
% 3.74/0.89      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.74/0.89      inference(unflattening,[status(thm)],[c_186]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_14,plain,
% 3.74/0.89      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 3.74/0.89      inference(cnf_transformation,[],[f60]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_491,plain,
% 3.74/0.89      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 3.74/0.89      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_720,plain,
% 3.74/0.89      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_187,c_491]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_1388,plain,
% 3.74/0.89      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.74/0.89      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_499,c_720]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_1377,plain,
% 3.74/0.89      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.74/0.89      | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_499,c_720]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_9,plain,
% 3.74/0.89      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK3(X1,X2,X0),X1) ),
% 3.74/0.89      inference(cnf_transformation,[],[f59]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_495,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.74/0.89      | r2_hidden(sK3(X1,X2,X0),X1) = iProver_top ),
% 3.74/0.89      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_8,plain,
% 3.74/0.89      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X2) ),
% 3.74/0.89      inference(cnf_transformation,[],[f58]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_496,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.74/0.89      | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top ),
% 3.74/0.89      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_787,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_495,c_720]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_849,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_496,c_787]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_907,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_495,c_849]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_5044,plain,
% 3.74/0.89      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3) = k1_xboole_0 ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_1377,c_907]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_1078,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3),X4)) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_495,c_907]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_5054,plain,
% 3.74/0.89      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3),X4) = k1_xboole_0 ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_1377,c_1078]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_5077,plain,
% 3.74/0.89      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_5044,c_5054]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6291,plain,
% 3.74/0.89      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_1388,c_5077]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_18,negated_conjecture,
% 3.74/0.89      ( k1_xboole_0 = k2_zfmisc_1(sK5,sK6)
% 3.74/0.89      | k1_xboole_0 = sK5
% 3.74/0.89      | k1_xboole_0 = sK6 ),
% 3.74/0.89      inference(cnf_transformation,[],[f47]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_10,plain,
% 3.74/0.89      ( ~ r2_hidden(X0,X1)
% 3.74/0.89      | ~ r2_hidden(X2,X3)
% 3.74/0.89      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.74/0.89      inference(cnf_transformation,[],[f43]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_498,plain,
% 3.74/0.89      ( r2_hidden(X0,X1) != iProver_top
% 3.74/0.89      | r2_hidden(X2,X3) != iProver_top
% 3.74/0.89      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.74/0.89      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_1292,plain,
% 3.74/0.89      ( sK5 = k1_xboole_0
% 3.74/0.89      | sK6 = k1_xboole_0
% 3.74/0.89      | r2_hidden(X0,sK5) != iProver_top
% 3.74/0.89      | r2_hidden(X1,sK6) != iProver_top
% 3.74/0.89      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_18,c_498]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_1577,plain,
% 3.74/0.89      ( sK5 = k1_xboole_0
% 3.74/0.89      | sK6 = k1_xboole_0
% 3.74/0.89      | r2_hidden(X0,sK5) != iProver_top
% 3.74/0.89      | r2_hidden(X1,sK6) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_1292,c_720]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6296,plain,
% 3.74/0.89      ( sK5 = k1_xboole_0
% 3.74/0.89      | sK6 = k1_xboole_0
% 3.74/0.89      | r2_hidden(X0,sK6) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_6291,c_1577]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6618,plain,
% 3.74/0.89      ( sK5 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_6291,c_6296]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_17,negated_conjecture,
% 3.74/0.89      ( k1_xboole_0 != k2_zfmisc_1(sK5,sK6) | k1_xboole_0 != sK5 ),
% 3.74/0.89      inference(cnf_transformation,[],[f48]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6663,plain,
% 3.74/0.89      ( k2_zfmisc_1(k1_xboole_0,sK6) != k1_xboole_0
% 3.74/0.89      | sK5 != k1_xboole_0
% 3.74/0.89      | sK6 = k1_xboole_0 ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_6618,c_17]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6665,plain,
% 3.74/0.89      ( sK5 != k1_xboole_0 | sK6 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_6663,c_5077]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6666,plain,
% 3.74/0.89      ( sK5 != k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.74/0.89      inference(equality_resolution_simp,[status(thm)],[c_6665]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6667,plain,
% 3.74/0.89      ( sK6 = k1_xboole_0 ),
% 3.74/0.89      inference(global_propositional_subsumption,[status(thm)],[c_6666,c_6618]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_16,negated_conjecture,
% 3.74/0.89      ( k1_xboole_0 != k2_zfmisc_1(sK5,sK6) | k1_xboole_0 != sK6 ),
% 3.74/0.89      inference(cnf_transformation,[],[f49]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6671,plain,
% 3.74/0.89      ( k2_zfmisc_1(sK5,k1_xboole_0) != k1_xboole_0
% 3.74/0.89      | k1_xboole_0 != k1_xboole_0 ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_6667,c_16]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6672,plain,
% 3.74/0.89      ( k2_zfmisc_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 3.74/0.89      inference(equality_resolution_simp,[status(thm)],[c_6671]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_1077,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(k1_xboole_0,X3)),X4))) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_496,c_907]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6314,plain,
% 3.74/0.89      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) = k1_xboole_0 ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_6291,c_1077]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_850,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_495,c_787]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_957,plain,
% 3.74/0.89      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3))) != iProver_top ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_496,c_850]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_5045,plain,
% 3.74/0.89      ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)),X3) = k1_xboole_0 ),
% 3.74/0.89      inference(superposition,[status(thm)],[c_1377,c_957]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_5079,plain,
% 3.74/0.89      ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2) = k1_xboole_0 ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_5077,c_5045]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_5085,plain,
% 3.74/0.89      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_5079,c_5077]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6344,plain,
% 3.74/0.89      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_6314,c_5077,c_5085]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6673,plain,
% 3.74/0.89      ( k1_xboole_0 != k1_xboole_0 ),
% 3.74/0.89      inference(demodulation,[status(thm)],[c_6672,c_6344]) ).
% 3.74/0.89  
% 3.74/0.89  cnf(c_6674,plain,
% 3.74/0.89      ( $false ),
% 3.74/0.89      inference(equality_resolution_simp,[status(thm)],[c_6673]) ).
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.89  
% 3.74/0.89  ------                               Statistics
% 3.74/0.89  
% 3.74/0.89  ------ General
% 3.74/0.89  
% 3.74/0.89  abstr_ref_over_cycles:                  0
% 3.74/0.89  abstr_ref_under_cycles:                 0
% 3.74/0.89  gc_basic_clause_elim:                   0
% 3.74/0.89  forced_gc_time:                         0
% 3.74/0.89  parsing_time:                           0.01
% 3.74/0.89  unif_index_cands_time:                  0.
% 3.74/0.89  unif_index_add_time:                    0.
% 3.74/0.89  orderings_time:                         0.
% 3.74/0.89  out_proof_time:                         0.008
% 3.74/0.89  total_time:                             0.259
% 3.74/0.89  num_of_symbols:                         45
% 3.74/0.89  num_of_terms:                           10718
% 3.74/0.89  
% 3.74/0.89  ------ Preprocessing
% 3.74/0.89  
% 3.74/0.89  num_of_splits:                          0
% 3.74/0.89  num_of_split_atoms:                     0
% 3.74/0.89  num_of_reused_defs:                     0
% 3.74/0.89  num_eq_ax_congr_red:                    59
% 3.74/0.89  num_of_sem_filtered_clauses:            1
% 3.74/0.89  num_of_subtypes:                        0
% 3.74/0.89  monotx_restored_types:                  0
% 3.74/0.89  sat_num_of_epr_types:                   0
% 3.74/0.89  sat_num_of_non_cyclic_types:            0
% 3.74/0.89  sat_guarded_non_collapsed_types:        0
% 3.74/0.89  num_pure_diseq_elim:                    0
% 3.74/0.89  simp_replaced_by:                       0
% 3.74/0.89  res_preprocessed:                       82
% 3.74/0.89  prep_upred:                             0
% 3.74/0.89  prep_unflattend:                        2
% 3.74/0.89  smt_new_axioms:                         0
% 3.74/0.89  pred_elim_cands:                        1
% 3.74/0.89  pred_elim:                              1
% 3.74/0.89  pred_elim_cl:                           1
% 3.74/0.89  pred_elim_cycles:                       3
% 3.74/0.89  merged_defs:                            0
% 3.74/0.89  merged_defs_ncl:                        0
% 3.74/0.89  bin_hyper_res:                          0
% 3.74/0.89  prep_cycles:                            4
% 3.74/0.89  pred_elim_time:                         0.
% 3.74/0.89  splitting_time:                         0.
% 3.74/0.89  sem_filter_time:                        0.
% 3.74/0.89  monotx_time:                            0.
% 3.74/0.89  subtype_inf_time:                       0.
% 3.74/0.89  
% 3.74/0.89  ------ Problem properties
% 3.74/0.89  
% 3.74/0.89  clauses:                                17
% 3.74/0.89  conjectures:                            3
% 3.74/0.89  epr:                                    0
% 3.74/0.89  horn:                                   12
% 3.74/0.89  ground:                                 3
% 3.74/0.89  unary:                                  2
% 3.74/0.89  binary:                                 8
% 3.74/0.89  lits:                                   41
% 3.74/0.89  lits_eq:                                16
% 3.74/0.89  fd_pure:                                0
% 3.74/0.89  fd_pseudo:                              0
% 3.74/0.89  fd_cond:                                0
% 3.74/0.89  fd_pseudo_cond:                         5
% 3.74/0.89  ac_symbols:                             0
% 3.74/0.89  
% 3.74/0.89  ------ Propositional Solver
% 3.74/0.89  
% 3.74/0.89  prop_solver_calls:                      35
% 3.74/0.89  prop_fast_solver_calls:                 645
% 3.74/0.89  smt_solver_calls:                       0
% 3.74/0.89  smt_fast_solver_calls:                  0
% 3.74/0.89  prop_num_of_clauses:                    3508
% 3.74/0.89  prop_preprocess_simplified:             4898
% 3.74/0.89  prop_fo_subsumed:                       4
% 3.74/0.89  prop_solver_time:                       0.
% 3.74/0.89  smt_solver_time:                        0.
% 3.74/0.89  smt_fast_solver_time:                   0.
% 3.74/0.89  prop_fast_solver_time:                  0.
% 3.74/0.89  prop_unsat_core_time:                   0.
% 3.74/0.89  
% 3.74/0.89  ------ QBF
% 3.74/0.89  
% 3.74/0.89  qbf_q_res:                              0
% 3.74/0.89  qbf_num_tautologies:                    0
% 3.74/0.89  qbf_prep_cycles:                        0
% 3.74/0.89  
% 3.74/0.89  ------ BMC1
% 3.74/0.89  
% 3.74/0.89  bmc1_current_bound:                     -1
% 3.74/0.89  bmc1_last_solved_bound:                 -1
% 3.74/0.89  bmc1_unsat_core_size:                   -1
% 3.74/0.89  bmc1_unsat_core_parents_size:           -1
% 3.74/0.89  bmc1_merge_next_fun:                    0
% 3.74/0.89  bmc1_unsat_core_clauses_time:           0.
% 3.74/0.89  
% 3.74/0.89  ------ Instantiation
% 3.74/0.89  
% 3.74/0.89  inst_num_of_clauses:                    525
% 3.74/0.89  inst_num_in_passive:                    199
% 3.74/0.89  inst_num_in_active:                     239
% 3.74/0.89  inst_num_in_unprocessed:                87
% 3.74/0.89  inst_num_of_loops:                      400
% 3.74/0.89  inst_num_of_learning_restarts:          0
% 3.74/0.89  inst_num_moves_active_passive:          153
% 3.74/0.89  inst_lit_activity:                      0
% 3.74/0.89  inst_lit_activity_moves:                0
% 3.74/0.89  inst_num_tautologies:                   0
% 3.74/0.89  inst_num_prop_implied:                  0
% 3.74/0.89  inst_num_existing_simplified:           0
% 3.74/0.89  inst_num_eq_res_simplified:             0
% 3.74/0.89  inst_num_child_elim:                    0
% 3.74/0.89  inst_num_of_dismatching_blockings:      479
% 3.74/0.89  inst_num_of_non_proper_insts:           757
% 3.74/0.89  inst_num_of_duplicates:                 0
% 3.74/0.89  inst_inst_num_from_inst_to_res:         0
% 3.74/0.89  inst_dismatching_checking_time:         0.
% 3.74/0.89  
% 3.74/0.89  ------ Resolution
% 3.74/0.89  
% 3.74/0.89  res_num_of_clauses:                     0
% 3.74/0.89  res_num_in_passive:                     0
% 3.74/0.89  res_num_in_active:                      0
% 3.74/0.89  res_num_of_loops:                       86
% 3.74/0.89  res_forward_subset_subsumed:            63
% 3.74/0.89  res_backward_subset_subsumed:           2
% 3.74/0.89  res_forward_subsumed:                   0
% 3.74/0.89  res_backward_subsumed:                  0
% 3.74/0.89  res_forward_subsumption_resolution:     0
% 3.74/0.89  res_backward_subsumption_resolution:    0
% 3.74/0.89  res_clause_to_clause_subsumption:       1736
% 3.74/0.89  res_orphan_elimination:                 0
% 3.74/0.89  res_tautology_del:                      54
% 3.74/0.89  res_num_eq_res_simplified:              0
% 3.74/0.89  res_num_sel_changes:                    0
% 3.74/0.89  res_moves_from_active_to_pass:          0
% 3.74/0.89  
% 3.74/0.89  ------ Superposition
% 3.74/0.89  
% 3.74/0.89  sup_time_total:                         0.
% 3.74/0.89  sup_time_generating:                    0.
% 3.74/0.89  sup_time_sim_full:                      0.
% 3.74/0.89  sup_time_sim_immed:                     0.
% 3.74/0.89  
% 3.74/0.89  sup_num_of_clauses:                     495
% 3.74/0.89  sup_num_in_active:                      42
% 3.74/0.89  sup_num_in_passive:                     453
% 3.74/0.89  sup_num_of_loops:                       79
% 3.74/0.89  sup_fw_superposition:                   407
% 3.74/0.89  sup_bw_superposition:                   487
% 3.74/0.89  sup_immediate_simplified:               155
% 3.74/0.89  sup_given_eliminated:                   0
% 3.74/0.89  comparisons_done:                       0
% 3.74/0.89  comparisons_avoided:                    73
% 3.74/0.89  
% 3.74/0.89  ------ Simplifications
% 3.74/0.89  
% 3.74/0.89  
% 3.74/0.89  sim_fw_subset_subsumed:                 20
% 3.74/0.89  sim_bw_subset_subsumed:                 69
% 3.74/0.89  sim_fw_subsumed:                        73
% 3.74/0.89  sim_bw_subsumed:                        38
% 3.74/0.89  sim_fw_subsumption_res:                 0
% 3.74/0.89  sim_bw_subsumption_res:                 0
% 3.74/0.89  sim_tautology_del:                      8
% 3.74/0.89  sim_eq_tautology_del:                   16
% 3.74/0.89  sim_eq_res_simp:                        2
% 3.74/0.89  sim_fw_demodulated:                     51
% 3.74/0.89  sim_bw_demodulated:                     14
% 3.74/0.89  sim_light_normalised:                   5
% 3.74/0.89  sim_joinable_taut:                      0
% 3.74/0.89  sim_joinable_simp:                      0
% 3.74/0.89  sim_ac_normalised:                      0
% 3.74/0.89  sim_smt_subsumption:                    0
% 3.74/0.89  
%------------------------------------------------------------------------------
