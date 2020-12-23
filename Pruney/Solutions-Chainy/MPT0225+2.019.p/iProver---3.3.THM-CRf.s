%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:07 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 560 expanded)
%              Number of clauses        :   58 ( 133 expanded)
%              Number of leaves         :   15 ( 137 expanded)
%              Depth                    :   23
%              Number of atoms          :  298 (1533 expanded)
%              Number of equality atoms :  161 ( 563 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK2 = sK3
        | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) )
      & ( sK2 != sK3
        | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( sK2 = sK3
      | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) )
    & ( sK2 != sK3
      | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).

fof(f51,plain,
    ( sK2 = sK3
    | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,
    ( sK2 = sK3
    | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f51,f37,f54,f54,f54])).

fof(f50,plain,
    ( sK2 != sK3
    | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,
    ( sK2 != sK3
    | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f50,f37,f54,f54,f54])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f48,f54])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1412,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1404,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1410,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1629,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1410])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1407,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1416,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1555,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_1416])).

cnf(c_1578,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X2)) != iProver_top
    | r2_hidden(X2,k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1555])).

cnf(c_2120,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
    | r1_tarski(X0,X2) != iProver_top
    | r2_hidden(X1,k1_zfmisc_1(X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1629,c_1578])).

cnf(c_12001,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X1,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_2120])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1406,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12168,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12001,c_1406])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1413,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12398,plain,
    ( X0 = X1
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12168,c_1413])).

cnf(c_12358,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12168])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1415,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1414,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1591,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_1416])).

cnf(c_1638,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1415,c_1591])).

cnf(c_1684,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1638])).

cnf(c_1990,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_1410])).

cnf(c_2181,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
    | r1_tarski(X1,X2) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1990,c_1578])).

cnf(c_13210,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_2181])).

cnf(c_13381,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_13210,c_1406])).

cnf(c_13608,plain,
    ( X0 = X1
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13381,c_1413])).

cnf(c_13730,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13608])).

cnf(c_14632,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12398,c_12358,c_13730])).

cnf(c_14633,plain,
    ( X0 = X1
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(renaming,[status(thm)],[c_14632])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | sK2 = sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14637,plain,
    ( sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_14633,c_14])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14655,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_14637,c_15])).

cnf(c_14657,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_14655])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1411,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14967,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14657,c_1411])).

cnf(c_1639,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_1591])).

cnf(c_1709,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1639])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1405,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2237,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_1405])).

cnf(c_2308,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_2237])).

cnf(c_2350,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_2308])).

cnf(c_2671,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2350,c_1416])).

cnf(c_15021,plain,
    ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14967,c_2671])).

cnf(c_2334,plain,
    ( r1_tarski(sK2,sK2) != iProver_top
    | r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2308])).

cnf(c_43,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_45,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15021,c_2334,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:29:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.95/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/0.98  
% 3.95/0.98  ------  iProver source info
% 3.95/0.98  
% 3.95/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.95/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/0.98  git: non_committed_changes: false
% 3.95/0.98  git: last_make_outside_of_git: false
% 3.95/0.98  
% 3.95/0.98  ------ 
% 3.95/0.98  ------ Parsing...
% 3.95/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/0.98  ------ Proving...
% 3.95/0.98  ------ Problem Properties 
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  clauses                                 15
% 3.95/0.98  conjectures                             4
% 3.95/0.98  EPR                                     3
% 3.95/0.98  Horn                                    11
% 3.95/0.98  unary                                   1
% 3.95/0.98  binary                                  10
% 3.95/0.98  lits                                    33
% 3.95/0.98  lits eq                                 9
% 3.95/0.98  fd_pure                                 0
% 3.95/0.98  fd_pseudo                               0
% 3.95/0.98  fd_cond                                 0
% 3.95/0.98  fd_pseudo_cond                          3
% 3.95/0.98  AC symbols                              0
% 3.95/0.98  
% 3.95/0.98  ------ Input Options Time Limit: Unbounded
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.95/0.98  Current options:
% 3.95/0.98  ------ 
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ Proving...
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/0.98  
% 3.95/0.98  ------ Proving...
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/0.98  
% 3.95/0.98  ------ Proving...
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  % SZS status Theorem for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  fof(f2,axiom,(
% 3.95/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f21,plain,(
% 3.95/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.95/0.98    inference(nnf_transformation,[],[f2])).
% 3.95/0.98  
% 3.95/0.98  fof(f22,plain,(
% 3.95/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.95/0.98    inference(flattening,[],[f21])).
% 3.95/0.98  
% 3.95/0.98  fof(f34,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.95/0.98    inference(cnf_transformation,[],[f22])).
% 3.95/0.98  
% 3.95/0.98  fof(f62,plain,(
% 3.95/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.95/0.98    inference(equality_resolution,[],[f34])).
% 3.95/0.98  
% 3.95/0.98  fof(f11,axiom,(
% 3.95/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f17,plain,(
% 3.95/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.95/0.98    inference(ennf_transformation,[],[f11])).
% 3.95/0.98  
% 3.95/0.98  fof(f49,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f17])).
% 3.95/0.98  
% 3.95/0.98  fof(f5,axiom,(
% 3.95/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f40,plain,(
% 3.95/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f5])).
% 3.95/0.98  
% 3.95/0.98  fof(f6,axiom,(
% 3.95/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f41,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f6])).
% 3.95/0.98  
% 3.95/0.98  fof(f7,axiom,(
% 3.95/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f42,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f7])).
% 3.95/0.98  
% 3.95/0.98  fof(f8,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f43,plain,(
% 3.95/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f8])).
% 3.95/0.98  
% 3.95/0.98  fof(f52,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f42,f43])).
% 3.95/0.98  
% 3.95/0.98  fof(f53,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f41,f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f54,plain,(
% 3.95/0.98    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f40,f53])).
% 3.95/0.98  
% 3.95/0.98  fof(f58,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f49,f54])).
% 3.95/0.98  
% 3.95/0.98  fof(f4,axiom,(
% 3.95/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f23,plain,(
% 3.95/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.95/0.98    inference(nnf_transformation,[],[f4])).
% 3.95/0.98  
% 3.95/0.98  fof(f38,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f23])).
% 3.95/0.98  
% 3.95/0.98  fof(f3,axiom,(
% 3.95/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f37,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f3])).
% 3.95/0.98  
% 3.95/0.98  fof(f56,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f38,f37])).
% 3.95/0.98  
% 3.95/0.98  fof(f9,axiom,(
% 3.95/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f24,plain,(
% 3.95/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.95/0.98    inference(nnf_transformation,[],[f9])).
% 3.95/0.98  
% 3.95/0.98  fof(f25,plain,(
% 3.95/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.95/0.98    inference(rectify,[],[f24])).
% 3.95/0.98  
% 3.95/0.98  fof(f26,plain,(
% 3.95/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.95/0.98    introduced(choice_axiom,[])).
% 3.95/0.98  
% 3.95/0.98  fof(f27,plain,(
% 3.95/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 3.95/0.98  
% 3.95/0.98  fof(f45,plain,(
% 3.95/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.95/0.98    inference(cnf_transformation,[],[f27])).
% 3.95/0.98  
% 3.95/0.98  fof(f63,plain,(
% 3.95/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.95/0.98    inference(equality_resolution,[],[f45])).
% 3.95/0.98  
% 3.95/0.98  fof(f1,axiom,(
% 3.95/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f14,plain,(
% 3.95/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.95/0.98    inference(rectify,[],[f1])).
% 3.95/0.98  
% 3.95/0.98  fof(f15,plain,(
% 3.95/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.95/0.98    inference(ennf_transformation,[],[f14])).
% 3.95/0.98  
% 3.95/0.98  fof(f19,plain,(
% 3.95/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.95/0.98    introduced(choice_axiom,[])).
% 3.95/0.98  
% 3.95/0.98  fof(f20,plain,(
% 3.95/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).
% 3.95/0.98  
% 3.95/0.98  fof(f33,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f20])).
% 3.95/0.98  
% 3.95/0.98  fof(f44,plain,(
% 3.95/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.95/0.98    inference(cnf_transformation,[],[f27])).
% 3.95/0.98  
% 3.95/0.98  fof(f64,plain,(
% 3.95/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.95/0.98    inference(equality_resolution,[],[f44])).
% 3.95/0.98  
% 3.95/0.98  fof(f36,plain,(
% 3.95/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f22])).
% 3.95/0.98  
% 3.95/0.98  fof(f32,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f20])).
% 3.95/0.98  
% 3.95/0.98  fof(f31,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f20])).
% 3.95/0.98  
% 3.95/0.98  fof(f12,conjecture,(
% 3.95/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f13,negated_conjecture,(
% 3.95/0.98    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.95/0.98    inference(negated_conjecture,[],[f12])).
% 3.95/0.98  
% 3.95/0.98  fof(f18,plain,(
% 3.95/0.98    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 3.95/0.98    inference(ennf_transformation,[],[f13])).
% 3.95/0.98  
% 3.95/0.98  fof(f28,plain,(
% 3.95/0.98    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 3.95/0.98    inference(nnf_transformation,[],[f18])).
% 3.95/0.98  
% 3.95/0.98  fof(f29,plain,(
% 3.95/0.98    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)) & (sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)))),
% 3.95/0.98    introduced(choice_axiom,[])).
% 3.95/0.98  
% 3.95/0.98  fof(f30,plain,(
% 3.95/0.98    (sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)) & (sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 3.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).
% 3.95/0.98  
% 3.95/0.98  fof(f51,plain,(
% 3.95/0.98    sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)),
% 3.95/0.98    inference(cnf_transformation,[],[f30])).
% 3.95/0.98  
% 3.95/0.98  fof(f59,plain,(
% 3.95/0.98    sK2 = sK3 | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 3.95/0.98    inference(definition_unfolding,[],[f51,f37,f54,f54,f54])).
% 3.95/0.98  
% 3.95/0.98  fof(f50,plain,(
% 3.95/0.98    sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.95/0.98    inference(cnf_transformation,[],[f30])).
% 3.95/0.98  
% 3.95/0.98  fof(f60,plain,(
% 3.95/0.98    sK2 != sK3 | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 3.95/0.98    inference(definition_unfolding,[],[f50,f37,f54,f54,f54])).
% 3.95/0.98  
% 3.95/0.98  fof(f39,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.95/0.98    inference(cnf_transformation,[],[f23])).
% 3.95/0.98  
% 3.95/0.98  fof(f55,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 3.95/0.98    inference(definition_unfolding,[],[f39,f37])).
% 3.95/0.98  
% 3.95/0.98  fof(f10,axiom,(
% 3.95/0.98    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f16,plain,(
% 3.95/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.95/0.98    inference(ennf_transformation,[],[f10])).
% 3.95/0.98  
% 3.95/0.98  fof(f48,plain,(
% 3.95/0.98    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f16])).
% 3.95/0.98  
% 3.95/0.98  fof(f57,plain,(
% 3.95/0.98    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f48,f54])).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5,plain,
% 3.95/0.98      ( r1_tarski(X0,X0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1412,plain,
% 3.95/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_13,plain,
% 3.95/0.98      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1404,plain,
% 3.95/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.95/0.98      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_7,plain,
% 3.95/0.98      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1410,plain,
% 3.95/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 3.95/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1629,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.95/0.98      | r2_hidden(X0,X1) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1404,c_1410]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_10,plain,
% 3.95/0.98      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.95/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1407,plain,
% 3.95/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.95/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_0,negated_conjecture,
% 3.95/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1416,plain,
% 3.95/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.95/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.95/0.98      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1555,plain,
% 3.95/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.95/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.95/0.98      | r1_xboole_0(X2,k1_zfmisc_1(X1)) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1407,c_1416]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1578,plain,
% 3.95/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.95/0.98      | r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X2)) != iProver_top
% 3.95/0.98      | r2_hidden(X2,k1_zfmisc_1(X1)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1404,c_1555]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2120,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.95/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.95/0.98      | r2_hidden(X1,k1_zfmisc_1(X2)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1629,c_1578]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_12001,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.95/0.98      | r2_hidden(X1,k1_zfmisc_1(X0)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1412,c_2120]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_11,plain,
% 3.95/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.95/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1406,plain,
% 3.95/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.95/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_12168,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.95/0.98      | r1_tarski(X1,X0) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_12001,c_1406]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3,plain,
% 3.95/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.95/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1413,plain,
% 3.95/0.98      ( X0 = X1
% 3.95/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.95/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_12398,plain,
% 3.95/0.98      ( X0 = X1
% 3.95/0.98      | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1)
% 3.95/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_12168,c_1413]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_12358,plain,
% 3.95/0.98      ( r1_tarski(X0,X1)
% 3.95/0.98      | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1) ),
% 3.95/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_12168]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1,plain,
% 3.95/0.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1415,plain,
% 3.95/0.98      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.95/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2,plain,
% 3.95/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1414,plain,
% 3.95/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.95/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1591,plain,
% 3.95/0.98      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 3.95/0.98      | r1_xboole_0(X2,X0) != iProver_top
% 3.95/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1414,c_1416]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1638,plain,
% 3.95/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.95/0.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1415,c_1591]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1684,plain,
% 3.95/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.95/0.98      | r1_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1404,c_1638]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1990,plain,
% 3.95/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) = X0
% 3.95/0.98      | r2_hidden(X1,X0) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1684,c_1410]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2181,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.95/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.95/0.98      | r2_hidden(X0,k1_zfmisc_1(X2)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1990,c_1578]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_13210,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.95/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1412,c_2181]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_13381,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.95/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_13210,c_1406]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_13608,plain,
% 3.95/0.98      ( X0 = X1
% 3.95/0.98      | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1)
% 3.95/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_13381,c_1413]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_13730,plain,
% 3.95/0.98      ( ~ r1_tarski(X0,X1)
% 3.95/0.98      | X0 = X1
% 3.95/0.98      | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1) ),
% 3.95/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_13608]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14632,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1)
% 3.95/0.98      | X0 = X1 ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_12398,c_12358,c_13730]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14633,plain,
% 3.95/0.98      ( X0 = X1
% 3.95/0.98      | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X1) ),
% 3.95/0.98      inference(renaming,[status(thm)],[c_14632]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14,negated_conjecture,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
% 3.95/0.98      | sK2 = sK3 ),
% 3.95/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14637,plain,
% 3.95/0.98      ( sK3 = sK2 ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_14633,c_14]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_15,negated_conjecture,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
% 3.95/0.98      | sK2 != sK3 ),
% 3.95/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14655,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
% 3.95/0.98      | sK2 != sK2 ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_14637,c_15]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14657,plain,
% 3.95/0.98      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.95/0.98      inference(equality_resolution_simp,[status(thm)],[c_14655]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6,plain,
% 3.95/0.98      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1411,plain,
% 3.95/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 3.95/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14967,plain,
% 3.95/0.98      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_14657,c_1411]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1639,plain,
% 3.95/0.98      ( r1_xboole_0(X0,X0) != iProver_top
% 3.95/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1414,c_1591]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1709,plain,
% 3.95/0.98      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top
% 3.95/0.98      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1404,c_1639]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_12,negated_conjecture,
% 3.95/0.98      ( ~ r2_hidden(X0,X1)
% 3.95/0.98      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1405,plain,
% 3.95/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.95/0.98      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2237,plain,
% 3.95/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.95/0.98      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1709,c_1405]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2308,plain,
% 3.95/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.95/0.98      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1407,c_2237]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2350,plain,
% 3.95/0.98      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1412,c_2308]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2671,plain,
% 3.95/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.95/0.98      | r1_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_2350,c_1416]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_15021,plain,
% 3.95/0.98      ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_14967,c_2671]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2334,plain,
% 3.95/0.98      ( r1_tarski(sK2,sK2) != iProver_top
% 3.95/0.98      | r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_2308]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_43,plain,
% 3.95/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_45,plain,
% 3.95/0.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_43]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(contradiction,plain,
% 3.95/0.98      ( $false ),
% 3.95/0.98      inference(minisat,[status(thm)],[c_15021,c_2334,c_45]) ).
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  ------                               Statistics
% 3.95/0.98  
% 3.95/0.98  ------ Selected
% 3.95/0.98  
% 3.95/0.98  total_time:                             0.433
% 3.95/0.98  
%------------------------------------------------------------------------------
