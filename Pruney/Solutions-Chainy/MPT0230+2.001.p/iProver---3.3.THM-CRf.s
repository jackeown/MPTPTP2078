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
% DateTime   : Thu Dec  3 11:30:41 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  150 (6421 expanded)
%              Number of clauses        :   88 (1906 expanded)
%              Number of leaves         :   19 (1802 expanded)
%              Depth                    :   27
%              Number of atoms          :  311 (8603 expanded)
%              Number of equality atoms :  248 (6874 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f39,f35,f35])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f57,f57])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f28])).

fof(f54,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f57,f50])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f58,f53])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f79,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f80,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5))))) ),
    inference(equality_resolution,[],[f79])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f81,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f56,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1319,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_1780,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1319,c_0])).

cnf(c_1975,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_1780])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1462,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_9508,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X0))) ),
    inference(superposition,[status(thm)],[c_1975,c_1462])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_900,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_899,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2231,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_900,c_899])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_898,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2232,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_898,c_899])).

cnf(c_1979,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1780,c_0])).

cnf(c_2225,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1975,c_0])).

cnf(c_2280,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1979,c_2225,c_2231])).

cnf(c_2285,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_2280])).

cnf(c_2303,plain,
    ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2285,c_2232])).

cnf(c_1321,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_2290,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,X0)))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_2280,c_1321])).

cnf(c_2376,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(light_normalisation,[status(thm)],[c_2290,c_2303])).

cnf(c_2305,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2303,c_2280])).

cnf(c_2377,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2376,c_9,c_2303,c_2305])).

cnf(c_3259,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_2377])).

cnf(c_3276,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3259,c_2232])).

cnf(c_9559,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9508,c_9,c_1975,c_2231,c_2232,c_2303,c_3276])).

cnf(c_9560,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_9559,c_2231])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_889,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2233,plain,
    ( k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)) = k2_tarski(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_889,c_899])).

cnf(c_2366,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_2233,c_1321])).

cnf(c_2383,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_2366,c_2])).

cnf(c_2382,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_2366,c_0])).

cnf(c_2597,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_3,c_2382])).

cnf(c_2602,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_2597,c_2233])).

cnf(c_2735,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_3,c_2602])).

cnf(c_2740,plain,
    ( k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2735,c_2233])).

cnf(c_2751,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))))) = k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2740,c_1321])).

cnf(c_2754,plain,
    ( k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK3)) = k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_2751,c_9,c_2303,c_2305])).

cnf(c_1464,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_3404,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1975,c_1464])).

cnf(c_1228,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_9])).

cnf(c_1320,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1228,c_0])).

cnf(c_1324,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1320,c_1228])).

cnf(c_1622,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1324,c_9])).

cnf(c_3421,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_3404,c_1622,c_2231,c_2232,c_3276])).

cnf(c_3408,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) ),
    inference(superposition,[status(thm)],[c_2740,c_1464])).

cnf(c_2745,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_2740,c_2366])).

cnf(c_3416,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_3408,c_2740,c_2745])).

cnf(c_3417,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_3416,c_2303])).

cnf(c_3418,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3417,c_3276])).

cnf(c_3422,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_3421,c_3418])).

cnf(c_4030,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_2383,c_2383,c_2754,c_3422])).

cnf(c_4031,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4030,c_2303])).

cnf(c_4032,plain,
    ( k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4031,c_3276])).

cnf(c_10826,plain,
    ( k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) = k2_tarski(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_9560,c_4032])).

cnf(c_2367,plain,
    ( k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_2233,c_2])).

cnf(c_18,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2368,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0)) = k3_enumset1(sK1,sK1,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_2367,c_18,c_2303])).

cnf(c_2594,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k1_xboole_0,k2_tarski(sK1,sK1))) = k3_enumset1(sK1,sK1,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_3,c_2368])).

cnf(c_2596,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK2,sK3) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2594,c_2232])).

cnf(c_7134,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK2,sK3) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_2596,c_2596,c_4032])).

cnf(c_16,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_891,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1314,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_891,c_18])).

cnf(c_7135,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7134,c_1314])).

cnf(c_10939,plain,
    ( r2_hidden(sK1,k2_tarski(sK2,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10826,c_7135])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1617,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_18,c_1])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_890,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_902,plain,
    ( X0 = X1
    | X2 = X1
    | X3 = X1
    | r2_hidden(X1,k3_enumset1(X0,X0,X0,X2,X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_890,c_18])).

cnf(c_9360,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k2_tarski(X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1617,c_902])).

cnf(c_11119,plain,
    ( sK2 = sK1
    | sK3 = sK1 ),
    inference(superposition,[status(thm)],[c_10939,c_9360])).

cnf(c_681,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_939,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_940,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_931,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_932,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_28,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11119,c_940,c_932,c_28,c_25,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.56/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.50  
% 7.56/1.50  ------  iProver source info
% 7.56/1.50  
% 7.56/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.50  git: non_committed_changes: false
% 7.56/1.50  git: last_make_outside_of_git: false
% 7.56/1.50  
% 7.56/1.50  ------ 
% 7.56/1.50  
% 7.56/1.50  ------ Input Options
% 7.56/1.50  
% 7.56/1.50  --out_options                           all
% 7.56/1.50  --tptp_safe_out                         true
% 7.56/1.50  --problem_path                          ""
% 7.56/1.50  --include_path                          ""
% 7.56/1.50  --clausifier                            res/vclausify_rel
% 7.56/1.50  --clausifier_options                    ""
% 7.56/1.50  --stdin                                 false
% 7.56/1.50  --stats_out                             all
% 7.56/1.50  
% 7.56/1.50  ------ General Options
% 7.56/1.50  
% 7.56/1.50  --fof                                   false
% 7.56/1.50  --time_out_real                         305.
% 7.56/1.50  --time_out_virtual                      -1.
% 7.56/1.50  --symbol_type_check                     false
% 7.56/1.50  --clausify_out                          false
% 7.56/1.50  --sig_cnt_out                           false
% 7.56/1.50  --trig_cnt_out                          false
% 7.56/1.50  --trig_cnt_out_tolerance                1.
% 7.56/1.50  --trig_cnt_out_sk_spl                   false
% 7.56/1.50  --abstr_cl_out                          false
% 7.56/1.50  
% 7.56/1.50  ------ Global Options
% 7.56/1.50  
% 7.56/1.50  --schedule                              default
% 7.56/1.50  --add_important_lit                     false
% 7.56/1.50  --prop_solver_per_cl                    1000
% 7.56/1.50  --min_unsat_core                        false
% 7.56/1.50  --soft_assumptions                      false
% 7.56/1.50  --soft_lemma_size                       3
% 7.56/1.50  --prop_impl_unit_size                   0
% 7.56/1.50  --prop_impl_unit                        []
% 7.56/1.50  --share_sel_clauses                     true
% 7.56/1.50  --reset_solvers                         false
% 7.56/1.50  --bc_imp_inh                            [conj_cone]
% 7.56/1.50  --conj_cone_tolerance                   3.
% 7.56/1.50  --extra_neg_conj                        none
% 7.56/1.50  --large_theory_mode                     true
% 7.56/1.50  --prolific_symb_bound                   200
% 7.56/1.50  --lt_threshold                          2000
% 7.56/1.50  --clause_weak_htbl                      true
% 7.56/1.50  --gc_record_bc_elim                     false
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing Options
% 7.56/1.50  
% 7.56/1.50  --preprocessing_flag                    true
% 7.56/1.50  --time_out_prep_mult                    0.1
% 7.56/1.50  --splitting_mode                        input
% 7.56/1.50  --splitting_grd                         true
% 7.56/1.50  --splitting_cvd                         false
% 7.56/1.50  --splitting_cvd_svl                     false
% 7.56/1.50  --splitting_nvd                         32
% 7.56/1.50  --sub_typing                            true
% 7.56/1.50  --prep_gs_sim                           true
% 7.56/1.50  --prep_unflatten                        true
% 7.56/1.50  --prep_res_sim                          true
% 7.56/1.50  --prep_upred                            true
% 7.56/1.50  --prep_sem_filter                       exhaustive
% 7.56/1.50  --prep_sem_filter_out                   false
% 7.56/1.50  --pred_elim                             true
% 7.56/1.50  --res_sim_input                         true
% 7.56/1.50  --eq_ax_congr_red                       true
% 7.56/1.50  --pure_diseq_elim                       true
% 7.56/1.50  --brand_transform                       false
% 7.56/1.50  --non_eq_to_eq                          false
% 7.56/1.50  --prep_def_merge                        true
% 7.56/1.50  --prep_def_merge_prop_impl              false
% 7.56/1.50  --prep_def_merge_mbd                    true
% 7.56/1.50  --prep_def_merge_tr_red                 false
% 7.56/1.50  --prep_def_merge_tr_cl                  false
% 7.56/1.50  --smt_preprocessing                     true
% 7.56/1.50  --smt_ac_axioms                         fast
% 7.56/1.50  --preprocessed_out                      false
% 7.56/1.50  --preprocessed_stats                    false
% 7.56/1.50  
% 7.56/1.50  ------ Abstraction refinement Options
% 7.56/1.50  
% 7.56/1.50  --abstr_ref                             []
% 7.56/1.50  --abstr_ref_prep                        false
% 7.56/1.50  --abstr_ref_until_sat                   false
% 7.56/1.50  --abstr_ref_sig_restrict                funpre
% 7.56/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.56/1.50  --abstr_ref_under                       []
% 7.56/1.50  
% 7.56/1.50  ------ SAT Options
% 7.56/1.50  
% 7.56/1.50  --sat_mode                              false
% 7.56/1.50  --sat_fm_restart_options                ""
% 7.56/1.50  --sat_gr_def                            false
% 7.56/1.50  --sat_epr_types                         true
% 7.56/1.50  --sat_non_cyclic_types                  false
% 7.56/1.50  --sat_finite_models                     false
% 7.56/1.50  --sat_fm_lemmas                         false
% 7.56/1.50  --sat_fm_prep                           false
% 7.56/1.50  --sat_fm_uc_incr                        true
% 7.56/1.50  --sat_out_model                         small
% 7.56/1.50  --sat_out_clauses                       false
% 7.56/1.50  
% 7.56/1.50  ------ QBF Options
% 7.56/1.50  
% 7.56/1.50  --qbf_mode                              false
% 7.56/1.50  --qbf_elim_univ                         false
% 7.56/1.50  --qbf_dom_inst                          none
% 7.56/1.50  --qbf_dom_pre_inst                      false
% 7.56/1.50  --qbf_sk_in                             false
% 7.56/1.50  --qbf_pred_elim                         true
% 7.56/1.50  --qbf_split                             512
% 7.56/1.50  
% 7.56/1.50  ------ BMC1 Options
% 7.56/1.50  
% 7.56/1.50  --bmc1_incremental                      false
% 7.56/1.50  --bmc1_axioms                           reachable_all
% 7.56/1.50  --bmc1_min_bound                        0
% 7.56/1.50  --bmc1_max_bound                        -1
% 7.56/1.50  --bmc1_max_bound_default                -1
% 7.56/1.50  --bmc1_symbol_reachability              true
% 7.56/1.50  --bmc1_property_lemmas                  false
% 7.56/1.50  --bmc1_k_induction                      false
% 7.56/1.50  --bmc1_non_equiv_states                 false
% 7.56/1.50  --bmc1_deadlock                         false
% 7.56/1.50  --bmc1_ucm                              false
% 7.56/1.50  --bmc1_add_unsat_core                   none
% 7.56/1.50  --bmc1_unsat_core_children              false
% 7.56/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.56/1.50  --bmc1_out_stat                         full
% 7.56/1.50  --bmc1_ground_init                      false
% 7.56/1.50  --bmc1_pre_inst_next_state              false
% 7.56/1.50  --bmc1_pre_inst_state                   false
% 7.56/1.50  --bmc1_pre_inst_reach_state             false
% 7.56/1.50  --bmc1_out_unsat_core                   false
% 7.56/1.50  --bmc1_aig_witness_out                  false
% 7.56/1.50  --bmc1_verbose                          false
% 7.56/1.50  --bmc1_dump_clauses_tptp                false
% 7.56/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.56/1.50  --bmc1_dump_file                        -
% 7.56/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.56/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.56/1.50  --bmc1_ucm_extend_mode                  1
% 7.56/1.50  --bmc1_ucm_init_mode                    2
% 7.56/1.50  --bmc1_ucm_cone_mode                    none
% 7.56/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.56/1.50  --bmc1_ucm_relax_model                  4
% 7.56/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.56/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.56/1.50  --bmc1_ucm_layered_model                none
% 7.56/1.50  --bmc1_ucm_max_lemma_size               10
% 7.56/1.50  
% 7.56/1.50  ------ AIG Options
% 7.56/1.50  
% 7.56/1.50  --aig_mode                              false
% 7.56/1.50  
% 7.56/1.50  ------ Instantiation Options
% 7.56/1.50  
% 7.56/1.50  --instantiation_flag                    true
% 7.56/1.50  --inst_sos_flag                         true
% 7.56/1.50  --inst_sos_phase                        true
% 7.56/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.56/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.56/1.50  --inst_lit_sel_side                     num_symb
% 7.56/1.50  --inst_solver_per_active                1400
% 7.56/1.50  --inst_solver_calls_frac                1.
% 7.56/1.50  --inst_passive_queue_type               priority_queues
% 7.56/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.56/1.50  --inst_passive_queues_freq              [25;2]
% 7.56/1.50  --inst_dismatching                      true
% 7.56/1.50  --inst_eager_unprocessed_to_passive     true
% 7.56/1.50  --inst_prop_sim_given                   true
% 7.56/1.50  --inst_prop_sim_new                     false
% 7.56/1.50  --inst_subs_new                         false
% 7.56/1.50  --inst_eq_res_simp                      false
% 7.56/1.50  --inst_subs_given                       false
% 7.56/1.50  --inst_orphan_elimination               true
% 7.56/1.50  --inst_learning_loop_flag               true
% 7.56/1.50  --inst_learning_start                   3000
% 7.56/1.50  --inst_learning_factor                  2
% 7.56/1.50  --inst_start_prop_sim_after_learn       3
% 7.56/1.50  --inst_sel_renew                        solver
% 7.56/1.50  --inst_lit_activity_flag                true
% 7.56/1.50  --inst_restr_to_given                   false
% 7.56/1.50  --inst_activity_threshold               500
% 7.56/1.50  --inst_out_proof                        true
% 7.56/1.50  
% 7.56/1.50  ------ Resolution Options
% 7.56/1.50  
% 7.56/1.50  --resolution_flag                       true
% 7.56/1.50  --res_lit_sel                           adaptive
% 7.56/1.50  --res_lit_sel_side                      none
% 7.56/1.50  --res_ordering                          kbo
% 7.56/1.50  --res_to_prop_solver                    active
% 7.56/1.50  --res_prop_simpl_new                    false
% 7.56/1.50  --res_prop_simpl_given                  true
% 7.56/1.50  --res_passive_queue_type                priority_queues
% 7.56/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.56/1.50  --res_passive_queues_freq               [15;5]
% 7.56/1.50  --res_forward_subs                      full
% 7.56/1.50  --res_backward_subs                     full
% 7.56/1.50  --res_forward_subs_resolution           true
% 7.56/1.50  --res_backward_subs_resolution          true
% 7.56/1.50  --res_orphan_elimination                true
% 7.56/1.50  --res_time_limit                        2.
% 7.56/1.50  --res_out_proof                         true
% 7.56/1.50  
% 7.56/1.50  ------ Superposition Options
% 7.56/1.50  
% 7.56/1.50  --superposition_flag                    true
% 7.56/1.50  --sup_passive_queue_type                priority_queues
% 7.56/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.56/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.56/1.50  --demod_completeness_check              fast
% 7.56/1.50  --demod_use_ground                      true
% 7.56/1.50  --sup_to_prop_solver                    passive
% 7.56/1.50  --sup_prop_simpl_new                    true
% 7.56/1.50  --sup_prop_simpl_given                  true
% 7.56/1.50  --sup_fun_splitting                     true
% 7.56/1.50  --sup_smt_interval                      50000
% 7.56/1.50  
% 7.56/1.50  ------ Superposition Simplification Setup
% 7.56/1.50  
% 7.56/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.56/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.56/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.56/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.56/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.56/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.56/1.50  --sup_immed_triv                        [TrivRules]
% 7.56/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.50  --sup_immed_bw_main                     []
% 7.56/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.56/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.56/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.50  --sup_input_bw                          []
% 7.56/1.50  
% 7.56/1.50  ------ Combination Options
% 7.56/1.50  
% 7.56/1.50  --comb_res_mult                         3
% 7.56/1.50  --comb_sup_mult                         2
% 7.56/1.50  --comb_inst_mult                        10
% 7.56/1.50  
% 7.56/1.50  ------ Debug Options
% 7.56/1.50  
% 7.56/1.50  --dbg_backtrace                         false
% 7.56/1.50  --dbg_dump_prop_clauses                 false
% 7.56/1.50  --dbg_dump_prop_clauses_file            -
% 7.56/1.50  --dbg_out_stat                          false
% 7.56/1.50  ------ Parsing...
% 7.56/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.50  ------ Proving...
% 7.56/1.50  ------ Problem Properties 
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  clauses                                 21
% 7.56/1.50  conjectures                             3
% 7.56/1.50  EPR                                     5
% 7.56/1.50  Horn                                    19
% 7.56/1.50  unary                                   14
% 7.56/1.50  binary                                  1
% 7.56/1.50  lits                                    37
% 7.56/1.50  lits eq                                 23
% 7.56/1.50  fd_pure                                 0
% 7.56/1.50  fd_pseudo                               0
% 7.56/1.50  fd_cond                                 0
% 7.56/1.50  fd_pseudo_cond                          5
% 7.56/1.50  AC symbols                              0
% 7.56/1.50  
% 7.56/1.50  ------ Schedule dynamic 5 is on 
% 7.56/1.50  
% 7.56/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  ------ 
% 7.56/1.50  Current options:
% 7.56/1.50  ------ 
% 7.56/1.50  
% 7.56/1.50  ------ Input Options
% 7.56/1.50  
% 7.56/1.50  --out_options                           all
% 7.56/1.50  --tptp_safe_out                         true
% 7.56/1.50  --problem_path                          ""
% 7.56/1.50  --include_path                          ""
% 7.56/1.50  --clausifier                            res/vclausify_rel
% 7.56/1.50  --clausifier_options                    ""
% 7.56/1.50  --stdin                                 false
% 7.56/1.50  --stats_out                             all
% 7.56/1.50  
% 7.56/1.50  ------ General Options
% 7.56/1.50  
% 7.56/1.50  --fof                                   false
% 7.56/1.50  --time_out_real                         305.
% 7.56/1.50  --time_out_virtual                      -1.
% 7.56/1.50  --symbol_type_check                     false
% 7.56/1.50  --clausify_out                          false
% 7.56/1.50  --sig_cnt_out                           false
% 7.56/1.50  --trig_cnt_out                          false
% 7.56/1.50  --trig_cnt_out_tolerance                1.
% 7.56/1.50  --trig_cnt_out_sk_spl                   false
% 7.56/1.50  --abstr_cl_out                          false
% 7.56/1.50  
% 7.56/1.50  ------ Global Options
% 7.56/1.50  
% 7.56/1.50  --schedule                              default
% 7.56/1.50  --add_important_lit                     false
% 7.56/1.50  --prop_solver_per_cl                    1000
% 7.56/1.50  --min_unsat_core                        false
% 7.56/1.50  --soft_assumptions                      false
% 7.56/1.50  --soft_lemma_size                       3
% 7.56/1.50  --prop_impl_unit_size                   0
% 7.56/1.50  --prop_impl_unit                        []
% 7.56/1.50  --share_sel_clauses                     true
% 7.56/1.50  --reset_solvers                         false
% 7.56/1.50  --bc_imp_inh                            [conj_cone]
% 7.56/1.50  --conj_cone_tolerance                   3.
% 7.56/1.50  --extra_neg_conj                        none
% 7.56/1.50  --large_theory_mode                     true
% 7.56/1.50  --prolific_symb_bound                   200
% 7.56/1.50  --lt_threshold                          2000
% 7.56/1.50  --clause_weak_htbl                      true
% 7.56/1.50  --gc_record_bc_elim                     false
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing Options
% 7.56/1.50  
% 7.56/1.50  --preprocessing_flag                    true
% 7.56/1.50  --time_out_prep_mult                    0.1
% 7.56/1.50  --splitting_mode                        input
% 7.56/1.50  --splitting_grd                         true
% 7.56/1.50  --splitting_cvd                         false
% 7.56/1.50  --splitting_cvd_svl                     false
% 7.56/1.50  --splitting_nvd                         32
% 7.56/1.50  --sub_typing                            true
% 7.56/1.50  --prep_gs_sim                           true
% 7.56/1.50  --prep_unflatten                        true
% 7.56/1.50  --prep_res_sim                          true
% 7.56/1.50  --prep_upred                            true
% 7.56/1.50  --prep_sem_filter                       exhaustive
% 7.56/1.50  --prep_sem_filter_out                   false
% 7.56/1.50  --pred_elim                             true
% 7.56/1.50  --res_sim_input                         true
% 7.56/1.50  --eq_ax_congr_red                       true
% 7.56/1.50  --pure_diseq_elim                       true
% 7.56/1.50  --brand_transform                       false
% 7.56/1.50  --non_eq_to_eq                          false
% 7.56/1.50  --prep_def_merge                        true
% 7.56/1.50  --prep_def_merge_prop_impl              false
% 7.56/1.50  --prep_def_merge_mbd                    true
% 7.56/1.50  --prep_def_merge_tr_red                 false
% 7.56/1.50  --prep_def_merge_tr_cl                  false
% 7.56/1.50  --smt_preprocessing                     true
% 7.56/1.50  --smt_ac_axioms                         fast
% 7.56/1.50  --preprocessed_out                      false
% 7.56/1.50  --preprocessed_stats                    false
% 7.56/1.50  
% 7.56/1.50  ------ Abstraction refinement Options
% 7.56/1.50  
% 7.56/1.50  --abstr_ref                             []
% 7.56/1.50  --abstr_ref_prep                        false
% 7.56/1.50  --abstr_ref_until_sat                   false
% 7.56/1.50  --abstr_ref_sig_restrict                funpre
% 7.56/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.56/1.50  --abstr_ref_under                       []
% 7.56/1.50  
% 7.56/1.50  ------ SAT Options
% 7.56/1.50  
% 7.56/1.50  --sat_mode                              false
% 7.56/1.50  --sat_fm_restart_options                ""
% 7.56/1.50  --sat_gr_def                            false
% 7.56/1.50  --sat_epr_types                         true
% 7.56/1.50  --sat_non_cyclic_types                  false
% 7.56/1.50  --sat_finite_models                     false
% 7.56/1.50  --sat_fm_lemmas                         false
% 7.56/1.50  --sat_fm_prep                           false
% 7.56/1.50  --sat_fm_uc_incr                        true
% 7.56/1.50  --sat_out_model                         small
% 7.56/1.50  --sat_out_clauses                       false
% 7.56/1.50  
% 7.56/1.50  ------ QBF Options
% 7.56/1.50  
% 7.56/1.50  --qbf_mode                              false
% 7.56/1.50  --qbf_elim_univ                         false
% 7.56/1.50  --qbf_dom_inst                          none
% 7.56/1.50  --qbf_dom_pre_inst                      false
% 7.56/1.50  --qbf_sk_in                             false
% 7.56/1.50  --qbf_pred_elim                         true
% 7.56/1.50  --qbf_split                             512
% 7.56/1.50  
% 7.56/1.50  ------ BMC1 Options
% 7.56/1.50  
% 7.56/1.50  --bmc1_incremental                      false
% 7.56/1.50  --bmc1_axioms                           reachable_all
% 7.56/1.50  --bmc1_min_bound                        0
% 7.56/1.50  --bmc1_max_bound                        -1
% 7.56/1.50  --bmc1_max_bound_default                -1
% 7.56/1.50  --bmc1_symbol_reachability              true
% 7.56/1.50  --bmc1_property_lemmas                  false
% 7.56/1.50  --bmc1_k_induction                      false
% 7.56/1.50  --bmc1_non_equiv_states                 false
% 7.56/1.50  --bmc1_deadlock                         false
% 7.56/1.50  --bmc1_ucm                              false
% 7.56/1.50  --bmc1_add_unsat_core                   none
% 7.56/1.50  --bmc1_unsat_core_children              false
% 7.56/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.56/1.50  --bmc1_out_stat                         full
% 7.56/1.50  --bmc1_ground_init                      false
% 7.56/1.50  --bmc1_pre_inst_next_state              false
% 7.56/1.50  --bmc1_pre_inst_state                   false
% 7.56/1.50  --bmc1_pre_inst_reach_state             false
% 7.56/1.50  --bmc1_out_unsat_core                   false
% 7.56/1.50  --bmc1_aig_witness_out                  false
% 7.56/1.50  --bmc1_verbose                          false
% 7.56/1.50  --bmc1_dump_clauses_tptp                false
% 7.56/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.56/1.50  --bmc1_dump_file                        -
% 7.56/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.56/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.56/1.50  --bmc1_ucm_extend_mode                  1
% 7.56/1.50  --bmc1_ucm_init_mode                    2
% 7.56/1.50  --bmc1_ucm_cone_mode                    none
% 7.56/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.56/1.50  --bmc1_ucm_relax_model                  4
% 7.56/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.56/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.56/1.50  --bmc1_ucm_layered_model                none
% 7.56/1.50  --bmc1_ucm_max_lemma_size               10
% 7.56/1.50  
% 7.56/1.50  ------ AIG Options
% 7.56/1.50  
% 7.56/1.50  --aig_mode                              false
% 7.56/1.50  
% 7.56/1.50  ------ Instantiation Options
% 7.56/1.50  
% 7.56/1.50  --instantiation_flag                    true
% 7.56/1.50  --inst_sos_flag                         true
% 7.56/1.50  --inst_sos_phase                        true
% 7.56/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.56/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.56/1.50  --inst_lit_sel_side                     none
% 7.56/1.50  --inst_solver_per_active                1400
% 7.56/1.50  --inst_solver_calls_frac                1.
% 7.56/1.50  --inst_passive_queue_type               priority_queues
% 7.56/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.56/1.50  --inst_passive_queues_freq              [25;2]
% 7.56/1.50  --inst_dismatching                      true
% 7.56/1.50  --inst_eager_unprocessed_to_passive     true
% 7.56/1.50  --inst_prop_sim_given                   true
% 7.56/1.50  --inst_prop_sim_new                     false
% 7.56/1.50  --inst_subs_new                         false
% 7.56/1.50  --inst_eq_res_simp                      false
% 7.56/1.50  --inst_subs_given                       false
% 7.56/1.50  --inst_orphan_elimination               true
% 7.56/1.50  --inst_learning_loop_flag               true
% 7.56/1.50  --inst_learning_start                   3000
% 7.56/1.50  --inst_learning_factor                  2
% 7.56/1.50  --inst_start_prop_sim_after_learn       3
% 7.56/1.50  --inst_sel_renew                        solver
% 7.56/1.50  --inst_lit_activity_flag                true
% 7.56/1.50  --inst_restr_to_given                   false
% 7.56/1.50  --inst_activity_threshold               500
% 7.56/1.50  --inst_out_proof                        true
% 7.56/1.50  
% 7.56/1.50  ------ Resolution Options
% 7.56/1.50  
% 7.56/1.50  --resolution_flag                       false
% 7.56/1.50  --res_lit_sel                           adaptive
% 7.56/1.50  --res_lit_sel_side                      none
% 7.56/1.50  --res_ordering                          kbo
% 7.56/1.50  --res_to_prop_solver                    active
% 7.56/1.50  --res_prop_simpl_new                    false
% 7.56/1.50  --res_prop_simpl_given                  true
% 7.56/1.50  --res_passive_queue_type                priority_queues
% 7.56/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.56/1.50  --res_passive_queues_freq               [15;5]
% 7.56/1.50  --res_forward_subs                      full
% 7.56/1.50  --res_backward_subs                     full
% 7.56/1.50  --res_forward_subs_resolution           true
% 7.56/1.50  --res_backward_subs_resolution          true
% 7.56/1.50  --res_orphan_elimination                true
% 7.56/1.50  --res_time_limit                        2.
% 7.56/1.50  --res_out_proof                         true
% 7.56/1.50  
% 7.56/1.50  ------ Superposition Options
% 7.56/1.50  
% 7.56/1.50  --superposition_flag                    true
% 7.56/1.50  --sup_passive_queue_type                priority_queues
% 7.56/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.56/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.56/1.50  --demod_completeness_check              fast
% 7.56/1.50  --demod_use_ground                      true
% 7.56/1.50  --sup_to_prop_solver                    passive
% 7.56/1.50  --sup_prop_simpl_new                    true
% 7.56/1.50  --sup_prop_simpl_given                  true
% 7.56/1.50  --sup_fun_splitting                     true
% 7.56/1.50  --sup_smt_interval                      50000
% 7.56/1.50  
% 7.56/1.50  ------ Superposition Simplification Setup
% 7.56/1.50  
% 7.56/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.56/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.56/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.56/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.56/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.56/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.56/1.50  --sup_immed_triv                        [TrivRules]
% 7.56/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.50  --sup_immed_bw_main                     []
% 7.56/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.56/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.56/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.50  --sup_input_bw                          []
% 7.56/1.50  
% 7.56/1.50  ------ Combination Options
% 7.56/1.50  
% 7.56/1.50  --comb_res_mult                         3
% 7.56/1.50  --comb_sup_mult                         2
% 7.56/1.50  --comb_inst_mult                        10
% 7.56/1.50  
% 7.56/1.50  ------ Debug Options
% 7.56/1.50  
% 7.56/1.50  --dbg_backtrace                         false
% 7.56/1.50  --dbg_dump_prop_clauses                 false
% 7.56/1.50  --dbg_dump_prop_clauses_file            -
% 7.56/1.50  --dbg_out_stat                          false
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  ------ Proving...
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  % SZS status Theorem for theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  fof(f2,axiom,(
% 7.56/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f31,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f2])).
% 7.56/1.50  
% 7.56/1.50  fof(f7,axiom,(
% 7.56/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f38,plain,(
% 7.56/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.56/1.50    inference(cnf_transformation,[],[f7])).
% 7.56/1.50  
% 7.56/1.50  fof(f4,axiom,(
% 7.56/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f35,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.56/1.50    inference(cnf_transformation,[],[f4])).
% 7.56/1.50  
% 7.56/1.50  fof(f62,plain,(
% 7.56/1.50    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 7.56/1.50    inference(definition_unfolding,[],[f38,f35])).
% 7.56/1.50  
% 7.56/1.50  fof(f8,axiom,(
% 7.56/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f39,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.56/1.50    inference(cnf_transformation,[],[f8])).
% 7.56/1.50  
% 7.56/1.50  fof(f59,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 7.56/1.50    inference(definition_unfolding,[],[f39,f35,f35])).
% 7.56/1.50  
% 7.56/1.50  fof(f1,axiom,(
% 7.56/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f30,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f1])).
% 7.56/1.50  
% 7.56/1.50  fof(f9,axiom,(
% 7.56/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f40,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.56/1.50    inference(cnf_transformation,[],[f9])).
% 7.56/1.50  
% 7.56/1.50  fof(f57,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.56/1.50    inference(definition_unfolding,[],[f40,f35])).
% 7.56/1.50  
% 7.56/1.50  fof(f61,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.56/1.50    inference(definition_unfolding,[],[f30,f57,f57])).
% 7.56/1.50  
% 7.56/1.50  fof(f3,axiom,(
% 7.56/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f21,plain,(
% 7.56/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.56/1.50    inference(nnf_transformation,[],[f3])).
% 7.56/1.50  
% 7.56/1.50  fof(f22,plain,(
% 7.56/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.56/1.50    inference(flattening,[],[f21])).
% 7.56/1.50  
% 7.56/1.50  fof(f32,plain,(
% 7.56/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.56/1.50    inference(cnf_transformation,[],[f22])).
% 7.56/1.50  
% 7.56/1.50  fof(f74,plain,(
% 7.56/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.56/1.50    inference(equality_resolution,[],[f32])).
% 7.56/1.50  
% 7.56/1.50  fof(f5,axiom,(
% 7.56/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f18,plain,(
% 7.56/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.56/1.50    inference(ennf_transformation,[],[f5])).
% 7.56/1.50  
% 7.56/1.50  fof(f36,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f18])).
% 7.56/1.50  
% 7.56/1.50  fof(f6,axiom,(
% 7.56/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f37,plain,(
% 7.56/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f6])).
% 7.56/1.50  
% 7.56/1.50  fof(f16,conjecture,(
% 7.56/1.50    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f17,negated_conjecture,(
% 7.56/1.50    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 7.56/1.50    inference(negated_conjecture,[],[f16])).
% 7.56/1.50  
% 7.56/1.50  fof(f20,plain,(
% 7.56/1.50    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f17])).
% 7.56/1.50  
% 7.56/1.50  fof(f28,plain,(
% 7.56/1.50    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f29,plain,(
% 7.56/1.50    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 7.56/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f28])).
% 7.56/1.50  
% 7.56/1.50  fof(f54,plain,(
% 7.56/1.50    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f12,axiom,(
% 7.56/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f50,plain,(
% 7.56/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f12])).
% 7.56/1.50  
% 7.56/1.50  fof(f72,plain,(
% 7.56/1.50    r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3))),
% 7.56/1.50    inference(definition_unfolding,[],[f54,f50])).
% 7.56/1.50  
% 7.56/1.50  fof(f14,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f52,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f14])).
% 7.56/1.50  
% 7.56/1.50  fof(f11,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f49,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f11])).
% 7.56/1.50  
% 7.56/1.50  fof(f58,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f49,f57,f50])).
% 7.56/1.50  
% 7.56/1.50  fof(f15,axiom,(
% 7.56/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f53,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f15])).
% 7.56/1.50  
% 7.56/1.50  fof(f71,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f52,f58,f53])).
% 7.56/1.50  
% 7.56/1.50  fof(f10,axiom,(
% 7.56/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f19,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.56/1.50    inference(ennf_transformation,[],[f10])).
% 7.56/1.50  
% 7.56/1.50  fof(f23,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.56/1.50    inference(nnf_transformation,[],[f19])).
% 7.56/1.50  
% 7.56/1.50  fof(f24,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.56/1.50    inference(flattening,[],[f23])).
% 7.56/1.50  
% 7.56/1.50  fof(f25,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.56/1.50    inference(rectify,[],[f24])).
% 7.56/1.50  
% 7.56/1.50  fof(f26,plain,(
% 7.56/1.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f27,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.56/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.56/1.50  
% 7.56/1.50  fof(f42,plain,(
% 7.56/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.56/1.50    inference(cnf_transformation,[],[f27])).
% 7.56/1.50  
% 7.56/1.50  fof(f69,plain,(
% 7.56/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 7.56/1.50    inference(definition_unfolding,[],[f42,f58])).
% 7.56/1.50  
% 7.56/1.50  fof(f79,plain,(
% 7.56/1.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3) )),
% 7.56/1.50    inference(equality_resolution,[],[f69])).
% 7.56/1.50  
% 7.56/1.50  fof(f80,plain,(
% 7.56/1.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))))) )),
% 7.56/1.50    inference(equality_resolution,[],[f79])).
% 7.56/1.50  
% 7.56/1.50  fof(f13,axiom,(
% 7.56/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f51,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f13])).
% 7.56/1.50  
% 7.56/1.50  fof(f60,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f51,f58])).
% 7.56/1.50  
% 7.56/1.50  fof(f41,plain,(
% 7.56/1.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.56/1.50    inference(cnf_transformation,[],[f27])).
% 7.56/1.50  
% 7.56/1.50  fof(f70,plain,(
% 7.56/1.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 7.56/1.50    inference(definition_unfolding,[],[f41,f58])).
% 7.56/1.50  
% 7.56/1.50  fof(f81,plain,(
% 7.56/1.50    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 7.56/1.50    inference(equality_resolution,[],[f70])).
% 7.56/1.50  
% 7.56/1.50  fof(f56,plain,(
% 7.56/1.50    sK1 != sK3),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f55,plain,(
% 7.56/1.50    sK1 != sK2),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3,plain,
% 7.56/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.56/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_0,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1319,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1780,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1319,c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1975,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_1780]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.56/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1462,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9508,plain,
% 7.56/1.50      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X0))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1975,c_1462]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6,plain,
% 7.56/1.50      ( r1_tarski(X0,X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_900,plain,
% 7.56/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7,plain,
% 7.56/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.56/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_899,plain,
% 7.56/1.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2231,plain,
% 7.56/1.50      ( k3_xboole_0(X0,X0) = X0 ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_900,c_899]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8,plain,
% 7.56/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_898,plain,
% 7.56/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2232,plain,
% 7.56/1.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_898,c_899]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1979,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1780,c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2225,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1975,c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2280,plain,
% 7.56/1.50      ( k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,X0) ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_1979,c_2225,c_2231]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2285,plain,
% 7.56/1.50      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_2280]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2303,plain,
% 7.56/1.50      ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_2285,c_2232]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1321,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2290,plain,
% 7.56/1.50      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,X0)))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_2280,c_1321]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2376,plain,
% 7.56/1.50      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_2290,c_2303]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2305,plain,
% 7.56/1.50      ( k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_2303,c_2280]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2377,plain,
% 7.56/1.50      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_2376,c_9,c_2303,c_2305]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3259,plain,
% 7.56/1.50      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_2377]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3276,plain,
% 7.56/1.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_3259,c_2232]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9559,plain,
% 7.56/1.50      ( k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0 ),
% 7.56/1.50      inference(light_normalisation,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_9508,c_9,c_1975,c_2231,c_2232,c_2303,c_3276]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9560,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_9559,c_2231]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_21,negated_conjecture,
% 7.56/1.50      ( r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)) ),
% 7.56/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_889,plain,
% 7.56/1.50      ( r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2233,plain,
% 7.56/1.50      ( k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)) = k2_tarski(sK1,sK1) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_889,c_899]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2366,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_2233,c_1321]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2383,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_2366,c_2]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2382,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_2366,c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2597,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_2382]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2602,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_2597,c_2233]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2735,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_2602]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2740,plain,
% 7.56/1.50      ( k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_2735,c_2233]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2751,plain,
% 7.56/1.50      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))))) = k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK3)) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_2740,c_1321]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2754,plain,
% 7.56/1.50      ( k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK3)) = k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_2751,c_9,c_2303,c_2305]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1464,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3404,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,X0)) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1975,c_1464]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1228,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_9]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1320,plain,
% 7.56/1.50      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1228,c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1324,plain,
% 7.56/1.50      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_1320,c_1228]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1622,plain,
% 7.56/1.50      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1324,c_9]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3421,plain,
% 7.56/1.50      ( k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.56/1.50      inference(light_normalisation,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_3404,c_1622,c_2231,c_2232,c_3276]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3408,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_2740,c_1464]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2745,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_2740,c_2366]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3416,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_3408,c_2740,c_2745]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3417,plain,
% 7.56/1.50      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k1_xboole_0)) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_3416,c_2303]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3418,plain,
% 7.56/1.50      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_3417,c_3276]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3422,plain,
% 7.56/1.50      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_3421,c_3418]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_4030,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
% 7.56/1.50      inference(light_normalisation,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_2383,c_2383,c_2754,c_3422]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_4031,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_4030,c_2303]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_4032,plain,
% 7.56/1.50      ( k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_4031,c_3276]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10826,plain,
% 7.56/1.50      ( k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) = k2_tarski(sK2,sK3) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_9560,c_4032]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2367,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))) = k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_2233,c_2]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k3_enumset1(X0,X0,X0,X1,X2) ),
% 7.56/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2368,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0)) = k3_enumset1(sK1,sK1,sK1,sK2,sK3) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_2367,c_18,c_2303]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2594,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k1_xboole_0,k2_tarski(sK1,sK1))) = k3_enumset1(sK1,sK1,sK1,sK2,sK3) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3,c_2368]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2596,plain,
% 7.56/1.50      ( k3_enumset1(sK1,sK1,sK1,sK2,sK3) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_2594,c_2232]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7134,plain,
% 7.56/1.50      ( k3_enumset1(sK1,sK1,sK1,sK2,sK3) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_2596,c_2596,c_4032]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_16,plain,
% 7.56/1.50      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
% 7.56/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_891,plain,
% 7.56/1.50      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1314,plain,
% 7.56/1.50      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_891,c_18]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7135,plain,
% 7.56/1.50      ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3))) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_7134,c_1314]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10939,plain,
% 7.56/1.50      ( r2_hidden(sK1,k2_tarski(sK2,sK3)) = iProver_top ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_10826,c_7135]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1,plain,
% 7.56/1.50      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1617,plain,
% 7.56/1.50      ( k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_18,c_1]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_17,plain,
% 7.56/1.50      ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))
% 7.56/1.50      | X0 = X1
% 7.56/1.50      | X0 = X2
% 7.56/1.50      | X0 = X3 ),
% 7.56/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_890,plain,
% 7.56/1.50      ( X0 = X1
% 7.56/1.50      | X0 = X2
% 7.56/1.50      | X0 = X3
% 7.56/1.50      | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_902,plain,
% 7.56/1.50      ( X0 = X1
% 7.56/1.50      | X2 = X1
% 7.56/1.50      | X3 = X1
% 7.56/1.50      | r2_hidden(X1,k3_enumset1(X0,X0,X0,X2,X3)) != iProver_top ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_890,c_18]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9360,plain,
% 7.56/1.50      ( X0 = X1
% 7.56/1.50      | X2 = X1
% 7.56/1.50      | r2_hidden(X1,k2_tarski(X0,X2)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1617,c_902]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11119,plain,
% 7.56/1.50      ( sK2 = sK1 | sK3 = sK1 ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_10939,c_9360]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_681,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_939,plain,
% 7.56/1.50      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_681]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_940,plain,
% 7.56/1.50      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_939]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_931,plain,
% 7.56/1.50      ( sK3 != X0 | sK1 != X0 | sK1 = sK3 ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_681]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_932,plain,
% 7.56/1.50      ( sK3 != sK1 | sK1 = sK3 | sK1 != sK1 ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_931]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_28,plain,
% 7.56/1.50      ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_25,plain,
% 7.56/1.50      ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))))
% 7.56/1.50      | sK1 = sK1 ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_19,negated_conjecture,
% 7.56/1.50      ( sK1 != sK3 ),
% 7.56/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_20,negated_conjecture,
% 7.56/1.50      ( sK1 != sK2 ),
% 7.56/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(contradiction,plain,
% 7.56/1.50      ( $false ),
% 7.56/1.50      inference(minisat,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_11119,c_940,c_932,c_28,c_25,c_19,c_20]) ).
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  ------                               Statistics
% 7.56/1.50  
% 7.56/1.50  ------ General
% 7.56/1.50  
% 7.56/1.50  abstr_ref_over_cycles:                  0
% 7.56/1.50  abstr_ref_under_cycles:                 0
% 7.56/1.50  gc_basic_clause_elim:                   0
% 7.56/1.50  forced_gc_time:                         0
% 7.56/1.50  parsing_time:                           0.018
% 7.56/1.50  unif_index_cands_time:                  0.
% 7.56/1.50  unif_index_add_time:                    0.
% 7.56/1.50  orderings_time:                         0.
% 7.56/1.50  out_proof_time:                         0.009
% 7.56/1.50  total_time:                             0.518
% 7.56/1.50  num_of_symbols:                         42
% 7.56/1.50  num_of_terms:                           15543
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing
% 7.56/1.50  
% 7.56/1.50  num_of_splits:                          0
% 7.56/1.50  num_of_split_atoms:                     0
% 7.56/1.50  num_of_reused_defs:                     0
% 7.56/1.50  num_eq_ax_congr_red:                    27
% 7.56/1.50  num_of_sem_filtered_clauses:            1
% 7.56/1.50  num_of_subtypes:                        0
% 7.56/1.50  monotx_restored_types:                  0
% 7.56/1.50  sat_num_of_epr_types:                   0
% 7.56/1.50  sat_num_of_non_cyclic_types:            0
% 7.56/1.50  sat_guarded_non_collapsed_types:        0
% 7.56/1.50  num_pure_diseq_elim:                    0
% 7.56/1.50  simp_replaced_by:                       0
% 7.56/1.50  res_preprocessed:                       99
% 7.56/1.50  prep_upred:                             0
% 7.56/1.50  prep_unflattend:                        28
% 7.56/1.50  smt_new_axioms:                         0
% 7.56/1.50  pred_elim_cands:                        2
% 7.56/1.50  pred_elim:                              0
% 7.56/1.50  pred_elim_cl:                           0
% 7.56/1.50  pred_elim_cycles:                       2
% 7.56/1.50  merged_defs:                            0
% 7.56/1.50  merged_defs_ncl:                        0
% 7.56/1.50  bin_hyper_res:                          0
% 7.56/1.50  prep_cycles:                            4
% 7.56/1.50  pred_elim_time:                         0.012
% 7.56/1.50  splitting_time:                         0.
% 7.56/1.50  sem_filter_time:                        0.
% 7.56/1.50  monotx_time:                            0.
% 7.56/1.50  subtype_inf_time:                       0.
% 7.56/1.50  
% 7.56/1.50  ------ Problem properties
% 7.56/1.50  
% 7.56/1.50  clauses:                                21
% 7.56/1.50  conjectures:                            3
% 7.56/1.50  epr:                                    5
% 7.56/1.50  horn:                                   19
% 7.56/1.50  ground:                                 3
% 7.56/1.50  unary:                                  14
% 7.56/1.50  binary:                                 1
% 7.56/1.50  lits:                                   37
% 7.56/1.50  lits_eq:                                23
% 7.56/1.50  fd_pure:                                0
% 7.56/1.50  fd_pseudo:                              0
% 7.56/1.50  fd_cond:                                0
% 7.56/1.50  fd_pseudo_cond:                         5
% 7.56/1.50  ac_symbols:                             0
% 7.56/1.50  
% 7.56/1.50  ------ Propositional Solver
% 7.56/1.50  
% 7.56/1.50  prop_solver_calls:                      29
% 7.56/1.50  prop_fast_solver_calls:                 655
% 7.56/1.50  smt_solver_calls:                       0
% 7.56/1.50  smt_fast_solver_calls:                  0
% 7.56/1.50  prop_num_of_clauses:                    3698
% 7.56/1.50  prop_preprocess_simplified:             8783
% 7.56/1.50  prop_fo_subsumed:                       0
% 7.56/1.50  prop_solver_time:                       0.
% 7.56/1.50  smt_solver_time:                        0.
% 7.56/1.50  smt_fast_solver_time:                   0.
% 7.56/1.50  prop_fast_solver_time:                  0.
% 7.56/1.50  prop_unsat_core_time:                   0.
% 7.56/1.50  
% 7.56/1.50  ------ QBF
% 7.56/1.50  
% 7.56/1.50  qbf_q_res:                              0
% 7.56/1.50  qbf_num_tautologies:                    0
% 7.56/1.50  qbf_prep_cycles:                        0
% 7.56/1.50  
% 7.56/1.50  ------ BMC1
% 7.56/1.50  
% 7.56/1.50  bmc1_current_bound:                     -1
% 7.56/1.50  bmc1_last_solved_bound:                 -1
% 7.56/1.50  bmc1_unsat_core_size:                   -1
% 7.56/1.50  bmc1_unsat_core_parents_size:           -1
% 7.56/1.50  bmc1_merge_next_fun:                    0
% 7.56/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.56/1.50  
% 7.56/1.50  ------ Instantiation
% 7.56/1.50  
% 7.56/1.50  inst_num_of_clauses:                    1098
% 7.56/1.50  inst_num_in_passive:                    260
% 7.56/1.50  inst_num_in_active:                     537
% 7.56/1.50  inst_num_in_unprocessed:                301
% 7.56/1.50  inst_num_of_loops:                      590
% 7.56/1.50  inst_num_of_learning_restarts:          0
% 7.56/1.50  inst_num_moves_active_passive:          51
% 7.56/1.50  inst_lit_activity:                      0
% 7.56/1.50  inst_lit_activity_moves:                0
% 7.56/1.50  inst_num_tautologies:                   0
% 7.56/1.50  inst_num_prop_implied:                  0
% 7.56/1.50  inst_num_existing_simplified:           0
% 7.56/1.50  inst_num_eq_res_simplified:             0
% 7.56/1.50  inst_num_child_elim:                    0
% 7.56/1.50  inst_num_of_dismatching_blockings:      1462
% 7.56/1.50  inst_num_of_non_proper_insts:           1583
% 7.56/1.50  inst_num_of_duplicates:                 0
% 7.56/1.50  inst_inst_num_from_inst_to_res:         0
% 7.56/1.50  inst_dismatching_checking_time:         0.
% 7.56/1.50  
% 7.56/1.50  ------ Resolution
% 7.56/1.50  
% 7.56/1.50  res_num_of_clauses:                     0
% 7.56/1.50  res_num_in_passive:                     0
% 7.56/1.50  res_num_in_active:                      0
% 7.56/1.50  res_num_of_loops:                       103
% 7.56/1.50  res_forward_subset_subsumed:            724
% 7.56/1.50  res_backward_subset_subsumed:           2
% 7.56/1.50  res_forward_subsumed:                   0
% 7.56/1.50  res_backward_subsumed:                  0
% 7.56/1.50  res_forward_subsumption_resolution:     0
% 7.56/1.50  res_backward_subsumption_resolution:    0
% 7.56/1.50  res_clause_to_clause_subsumption:       1100
% 7.56/1.50  res_orphan_elimination:                 0
% 7.56/1.50  res_tautology_del:                      54
% 7.56/1.50  res_num_eq_res_simplified:              0
% 7.56/1.50  res_num_sel_changes:                    0
% 7.56/1.50  res_moves_from_active_to_pass:          0
% 7.56/1.50  
% 7.56/1.50  ------ Superposition
% 7.56/1.50  
% 7.56/1.50  sup_time_total:                         0.
% 7.56/1.50  sup_time_generating:                    0.
% 7.56/1.50  sup_time_sim_full:                      0.
% 7.56/1.50  sup_time_sim_immed:                     0.
% 7.56/1.50  
% 7.56/1.50  sup_num_of_clauses:                     187
% 7.56/1.50  sup_num_in_active:                      71
% 7.56/1.50  sup_num_in_passive:                     116
% 7.56/1.50  sup_num_of_loops:                       116
% 7.56/1.50  sup_fw_superposition:                   723
% 7.56/1.50  sup_bw_superposition:                   569
% 7.56/1.50  sup_immediate_simplified:               451
% 7.56/1.50  sup_given_eliminated:                   5
% 7.56/1.50  comparisons_done:                       0
% 7.56/1.50  comparisons_avoided:                    0
% 7.56/1.50  
% 7.56/1.50  ------ Simplifications
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  sim_fw_subset_subsumed:                 0
% 7.56/1.50  sim_bw_subset_subsumed:                 0
% 7.56/1.50  sim_fw_subsumed:                        13
% 7.56/1.50  sim_bw_subsumed:                        10
% 7.56/1.50  sim_fw_subsumption_res:                 0
% 7.56/1.50  sim_bw_subsumption_res:                 0
% 7.56/1.50  sim_tautology_del:                      0
% 7.56/1.50  sim_eq_tautology_del:                   245
% 7.56/1.50  sim_eq_res_simp:                        0
% 7.56/1.50  sim_fw_demodulated:                     199
% 7.56/1.50  sim_bw_demodulated:                     49
% 7.56/1.50  sim_light_normalised:                   370
% 7.56/1.50  sim_joinable_taut:                      0
% 7.56/1.50  sim_joinable_simp:                      0
% 7.56/1.50  sim_ac_normalised:                      0
% 7.56/1.50  sim_smt_subsumption:                    0
% 7.56/1.50  
%------------------------------------------------------------------------------
