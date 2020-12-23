%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:04 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :  141 (2432 expanded)
%              Number of clauses        :   83 ( 706 expanded)
%              Number of leaves         :   18 ( 586 expanded)
%              Depth                    :   27
%              Number of atoms          :  186 (3768 expanded)
%              Number of equality atoms :  133 (2219 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f39,f35,f35])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).

fof(f49,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f50,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(definition_unfolding,[],[f50,f42,f35,f53,f53])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f33,f35])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_805,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_11])).

cnf(c_1197,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[status(thm)],[c_9,c_805])).

cnf(c_10,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1210,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_1197,c_8,c_10])).

cnf(c_1298,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1210])).

cnf(c_1520,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1298,c_805])).

cnf(c_1521,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1520,c_8])).

cnf(c_5294,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1521,c_805])).

cnf(c_5304,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0),k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5294,c_8])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_142,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_143,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_428,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_430,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1412,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_428,c_430])).

cnf(c_1738,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_1412,c_9])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_429,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_808,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2))),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_429])).

cnf(c_3992,plain,
    ( r1_tarski(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),X1))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_808])).

cnf(c_1975,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X1)) = k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),X1) ),
    inference(superposition,[status(thm)],[c_1738,c_11])).

cnf(c_4019,plain,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),X1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3992,c_1975])).

cnf(c_938,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_4020,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X1))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4019,c_938])).

cnf(c_4021,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4020,c_1738])).

cnf(c_4924,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_4021])).

cnf(c_4946,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4924,c_1412])).

cnf(c_5090,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_4946,c_430])).

cnf(c_11221,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_5304,c_5090])).

cnf(c_11285,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(demodulation,[status(thm)],[c_11221,c_5304])).

cnf(c_1743,plain,
    ( k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1412,c_0])).

cnf(c_11286,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_11285,c_1412,c_1743])).

cnf(c_1969,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_1738])).

cnf(c_11749,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_11286,c_1969])).

cnf(c_4801,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X1)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_9,c_1975])).

cnf(c_4837,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X1)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ),
    inference(demodulation,[status(thm)],[c_4801,c_1738])).

cnf(c_6236,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) ),
    inference(superposition,[status(thm)],[c_1412,c_4837])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_433,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1410,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_433,c_430])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_432,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2860,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_433,c_432])).

cnf(c_2877,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2860,c_1410])).

cnf(c_2863,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_428,c_432])).

cnf(c_1971,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_1412,c_1738])).

cnf(c_1981,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_1971,c_1410])).

cnf(c_2874,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2863,c_1412,c_1981])).

cnf(c_2878,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2877,c_2874])).

cnf(c_6263,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(demodulation,[status(thm)],[c_6236,c_1410,c_2877,c_2878])).

cnf(c_7312,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6263,c_4946])).

cnf(c_7903,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_7312])).

cnf(c_7912,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7903,c_8,c_1410,c_1743,c_2877])).

cnf(c_8689,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7912,c_432])).

cnf(c_8690,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_7912,c_430])).

cnf(c_8691,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8689,c_8690])).

cnf(c_11753,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11749,c_1743,c_8691])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_572,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_14])).

cnf(c_802,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_11,c_572])).

cnf(c_1040,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) != sK1 ),
    inference(superposition,[status(thm)],[c_11,c_802])).

cnf(c_1850,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_1743,c_1040])).

cnf(c_2053,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(light_normalisation,[status(thm)],[c_1850,c_1981])).

cnf(c_13013,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)),k1_xboole_0)) != sK1 ),
    inference(demodulation,[status(thm)],[c_11753,c_2053])).

cnf(c_657,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_1198,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_657,c_805])).

cnf(c_1209,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1198,c_8])).

cnf(c_1290,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1209,c_805])).

cnf(c_1291,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1290,c_8])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_431,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2174,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_431])).

cnf(c_2210,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2174,c_430])).

cnf(c_4224,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1291,c_2210])).

cnf(c_13014,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1))) != sK1 ),
    inference(demodulation,[status(thm)],[c_13013,c_4224])).

cnf(c_13015,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_13014,c_2877,c_2878,c_4224])).

cnf(c_13016,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13015])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:59:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.46/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/1.52  
% 7.46/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.46/1.52  
% 7.46/1.52  ------  iProver source info
% 7.46/1.52  
% 7.46/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.46/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.46/1.52  git: non_committed_changes: false
% 7.46/1.52  git: last_make_outside_of_git: false
% 7.46/1.52  
% 7.46/1.52  ------ 
% 7.46/1.52  
% 7.46/1.52  ------ Input Options
% 7.46/1.52  
% 7.46/1.52  --out_options                           all
% 7.46/1.52  --tptp_safe_out                         true
% 7.46/1.52  --problem_path                          ""
% 7.46/1.52  --include_path                          ""
% 7.46/1.52  --clausifier                            res/vclausify_rel
% 7.46/1.52  --clausifier_options                    ""
% 7.46/1.52  --stdin                                 false
% 7.46/1.52  --stats_out                             all
% 7.46/1.52  
% 7.46/1.52  ------ General Options
% 7.46/1.52  
% 7.46/1.52  --fof                                   false
% 7.46/1.52  --time_out_real                         305.
% 7.46/1.52  --time_out_virtual                      -1.
% 7.46/1.52  --symbol_type_check                     false
% 7.46/1.52  --clausify_out                          false
% 7.46/1.52  --sig_cnt_out                           false
% 7.46/1.52  --trig_cnt_out                          false
% 7.46/1.52  --trig_cnt_out_tolerance                1.
% 7.46/1.52  --trig_cnt_out_sk_spl                   false
% 7.46/1.52  --abstr_cl_out                          false
% 7.46/1.52  
% 7.46/1.52  ------ Global Options
% 7.46/1.52  
% 7.46/1.52  --schedule                              default
% 7.46/1.52  --add_important_lit                     false
% 7.46/1.52  --prop_solver_per_cl                    1000
% 7.46/1.52  --min_unsat_core                        false
% 7.46/1.52  --soft_assumptions                      false
% 7.46/1.52  --soft_lemma_size                       3
% 7.46/1.52  --prop_impl_unit_size                   0
% 7.46/1.52  --prop_impl_unit                        []
% 7.46/1.52  --share_sel_clauses                     true
% 7.46/1.52  --reset_solvers                         false
% 7.46/1.52  --bc_imp_inh                            [conj_cone]
% 7.46/1.52  --conj_cone_tolerance                   3.
% 7.46/1.52  --extra_neg_conj                        none
% 7.46/1.52  --large_theory_mode                     true
% 7.46/1.52  --prolific_symb_bound                   200
% 7.46/1.52  --lt_threshold                          2000
% 7.46/1.52  --clause_weak_htbl                      true
% 7.46/1.52  --gc_record_bc_elim                     false
% 7.46/1.52  
% 7.46/1.52  ------ Preprocessing Options
% 7.46/1.52  
% 7.46/1.52  --preprocessing_flag                    true
% 7.46/1.52  --time_out_prep_mult                    0.1
% 7.46/1.52  --splitting_mode                        input
% 7.46/1.52  --splitting_grd                         true
% 7.46/1.52  --splitting_cvd                         false
% 7.46/1.52  --splitting_cvd_svl                     false
% 7.46/1.52  --splitting_nvd                         32
% 7.46/1.52  --sub_typing                            true
% 7.46/1.52  --prep_gs_sim                           true
% 7.46/1.52  --prep_unflatten                        true
% 7.46/1.52  --prep_res_sim                          true
% 7.46/1.52  --prep_upred                            true
% 7.46/1.52  --prep_sem_filter                       exhaustive
% 7.46/1.52  --prep_sem_filter_out                   false
% 7.46/1.52  --pred_elim                             true
% 7.46/1.52  --res_sim_input                         true
% 7.46/1.52  --eq_ax_congr_red                       true
% 7.46/1.52  --pure_diseq_elim                       true
% 7.46/1.52  --brand_transform                       false
% 7.46/1.52  --non_eq_to_eq                          false
% 7.46/1.52  --prep_def_merge                        true
% 7.46/1.52  --prep_def_merge_prop_impl              false
% 7.46/1.52  --prep_def_merge_mbd                    true
% 7.46/1.52  --prep_def_merge_tr_red                 false
% 7.46/1.52  --prep_def_merge_tr_cl                  false
% 7.46/1.52  --smt_preprocessing                     true
% 7.46/1.52  --smt_ac_axioms                         fast
% 7.46/1.52  --preprocessed_out                      false
% 7.46/1.52  --preprocessed_stats                    false
% 7.46/1.52  
% 7.46/1.52  ------ Abstraction refinement Options
% 7.46/1.52  
% 7.46/1.52  --abstr_ref                             []
% 7.46/1.52  --abstr_ref_prep                        false
% 7.46/1.52  --abstr_ref_until_sat                   false
% 7.46/1.52  --abstr_ref_sig_restrict                funpre
% 7.46/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.46/1.52  --abstr_ref_under                       []
% 7.46/1.52  
% 7.46/1.52  ------ SAT Options
% 7.46/1.52  
% 7.46/1.52  --sat_mode                              false
% 7.46/1.52  --sat_fm_restart_options                ""
% 7.46/1.52  --sat_gr_def                            false
% 7.46/1.52  --sat_epr_types                         true
% 7.46/1.52  --sat_non_cyclic_types                  false
% 7.46/1.52  --sat_finite_models                     false
% 7.46/1.52  --sat_fm_lemmas                         false
% 7.46/1.52  --sat_fm_prep                           false
% 7.46/1.52  --sat_fm_uc_incr                        true
% 7.46/1.52  --sat_out_model                         small
% 7.46/1.52  --sat_out_clauses                       false
% 7.46/1.52  
% 7.46/1.52  ------ QBF Options
% 7.46/1.52  
% 7.46/1.52  --qbf_mode                              false
% 7.46/1.52  --qbf_elim_univ                         false
% 7.46/1.52  --qbf_dom_inst                          none
% 7.46/1.52  --qbf_dom_pre_inst                      false
% 7.46/1.52  --qbf_sk_in                             false
% 7.46/1.52  --qbf_pred_elim                         true
% 7.46/1.52  --qbf_split                             512
% 7.46/1.52  
% 7.46/1.52  ------ BMC1 Options
% 7.46/1.52  
% 7.46/1.52  --bmc1_incremental                      false
% 7.46/1.52  --bmc1_axioms                           reachable_all
% 7.46/1.52  --bmc1_min_bound                        0
% 7.46/1.52  --bmc1_max_bound                        -1
% 7.46/1.52  --bmc1_max_bound_default                -1
% 7.46/1.52  --bmc1_symbol_reachability              true
% 7.46/1.52  --bmc1_property_lemmas                  false
% 7.46/1.52  --bmc1_k_induction                      false
% 7.46/1.52  --bmc1_non_equiv_states                 false
% 7.46/1.52  --bmc1_deadlock                         false
% 7.46/1.52  --bmc1_ucm                              false
% 7.46/1.52  --bmc1_add_unsat_core                   none
% 7.46/1.52  --bmc1_unsat_core_children              false
% 7.46/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.46/1.52  --bmc1_out_stat                         full
% 7.46/1.52  --bmc1_ground_init                      false
% 7.46/1.52  --bmc1_pre_inst_next_state              false
% 7.46/1.52  --bmc1_pre_inst_state                   false
% 7.46/1.52  --bmc1_pre_inst_reach_state             false
% 7.46/1.52  --bmc1_out_unsat_core                   false
% 7.46/1.52  --bmc1_aig_witness_out                  false
% 7.46/1.52  --bmc1_verbose                          false
% 7.46/1.52  --bmc1_dump_clauses_tptp                false
% 7.46/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.46/1.52  --bmc1_dump_file                        -
% 7.46/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.46/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.46/1.52  --bmc1_ucm_extend_mode                  1
% 7.46/1.52  --bmc1_ucm_init_mode                    2
% 7.46/1.52  --bmc1_ucm_cone_mode                    none
% 7.46/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.46/1.52  --bmc1_ucm_relax_model                  4
% 7.46/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.46/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.46/1.52  --bmc1_ucm_layered_model                none
% 7.46/1.52  --bmc1_ucm_max_lemma_size               10
% 7.46/1.52  
% 7.46/1.52  ------ AIG Options
% 7.46/1.52  
% 7.46/1.52  --aig_mode                              false
% 7.46/1.52  
% 7.46/1.52  ------ Instantiation Options
% 7.46/1.52  
% 7.46/1.52  --instantiation_flag                    true
% 7.46/1.52  --inst_sos_flag                         true
% 7.46/1.52  --inst_sos_phase                        true
% 7.46/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.46/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.46/1.52  --inst_lit_sel_side                     num_symb
% 7.46/1.52  --inst_solver_per_active                1400
% 7.46/1.52  --inst_solver_calls_frac                1.
% 7.46/1.52  --inst_passive_queue_type               priority_queues
% 7.46/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.46/1.52  --inst_passive_queues_freq              [25;2]
% 7.46/1.52  --inst_dismatching                      true
% 7.46/1.52  --inst_eager_unprocessed_to_passive     true
% 7.46/1.52  --inst_prop_sim_given                   true
% 7.46/1.52  --inst_prop_sim_new                     false
% 7.46/1.52  --inst_subs_new                         false
% 7.46/1.52  --inst_eq_res_simp                      false
% 7.46/1.52  --inst_subs_given                       false
% 7.46/1.52  --inst_orphan_elimination               true
% 7.46/1.52  --inst_learning_loop_flag               true
% 7.46/1.52  --inst_learning_start                   3000
% 7.46/1.52  --inst_learning_factor                  2
% 7.46/1.52  --inst_start_prop_sim_after_learn       3
% 7.46/1.52  --inst_sel_renew                        solver
% 7.46/1.52  --inst_lit_activity_flag                true
% 7.46/1.52  --inst_restr_to_given                   false
% 7.46/1.52  --inst_activity_threshold               500
% 7.46/1.52  --inst_out_proof                        true
% 7.46/1.52  
% 7.46/1.52  ------ Resolution Options
% 7.46/1.52  
% 7.46/1.52  --resolution_flag                       true
% 7.46/1.52  --res_lit_sel                           adaptive
% 7.46/1.52  --res_lit_sel_side                      none
% 7.46/1.52  --res_ordering                          kbo
% 7.46/1.52  --res_to_prop_solver                    active
% 7.46/1.52  --res_prop_simpl_new                    false
% 7.46/1.52  --res_prop_simpl_given                  true
% 7.46/1.52  --res_passive_queue_type                priority_queues
% 7.46/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.46/1.52  --res_passive_queues_freq               [15;5]
% 7.46/1.52  --res_forward_subs                      full
% 7.46/1.52  --res_backward_subs                     full
% 7.46/1.52  --res_forward_subs_resolution           true
% 7.46/1.52  --res_backward_subs_resolution          true
% 7.46/1.52  --res_orphan_elimination                true
% 7.46/1.52  --res_time_limit                        2.
% 7.46/1.52  --res_out_proof                         true
% 7.46/1.52  
% 7.46/1.52  ------ Superposition Options
% 7.46/1.52  
% 7.46/1.52  --superposition_flag                    true
% 7.46/1.52  --sup_passive_queue_type                priority_queues
% 7.46/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.46/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.46/1.52  --demod_completeness_check              fast
% 7.46/1.52  --demod_use_ground                      true
% 7.46/1.52  --sup_to_prop_solver                    passive
% 7.46/1.52  --sup_prop_simpl_new                    true
% 7.46/1.52  --sup_prop_simpl_given                  true
% 7.46/1.52  --sup_fun_splitting                     true
% 7.46/1.52  --sup_smt_interval                      50000
% 7.46/1.52  
% 7.46/1.52  ------ Superposition Simplification Setup
% 7.46/1.52  
% 7.46/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.46/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.46/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.46/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.46/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.46/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.46/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.46/1.52  --sup_immed_triv                        [TrivRules]
% 7.46/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.46/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.46/1.52  --sup_immed_bw_main                     []
% 7.46/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.46/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.46/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.46/1.52  --sup_input_bw                          []
% 7.46/1.52  
% 7.46/1.52  ------ Combination Options
% 7.46/1.52  
% 7.46/1.52  --comb_res_mult                         3
% 7.46/1.52  --comb_sup_mult                         2
% 7.46/1.52  --comb_inst_mult                        10
% 7.46/1.52  
% 7.46/1.52  ------ Debug Options
% 7.46/1.52  
% 7.46/1.52  --dbg_backtrace                         false
% 7.46/1.52  --dbg_dump_prop_clauses                 false
% 7.46/1.52  --dbg_dump_prop_clauses_file            -
% 7.46/1.52  --dbg_out_stat                          false
% 7.46/1.52  ------ Parsing...
% 7.46/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.46/1.52  
% 7.46/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.46/1.52  
% 7.46/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.46/1.52  
% 7.46/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.52  ------ Proving...
% 7.46/1.52  ------ Problem Properties 
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  clauses                                 14
% 7.46/1.52  conjectures                             1
% 7.46/1.52  EPR                                     2
% 7.46/1.52  Horn                                    14
% 7.46/1.52  unary                                   10
% 7.46/1.52  binary                                  3
% 7.46/1.52  lits                                    19
% 7.46/1.52  lits eq                                 11
% 7.46/1.52  fd_pure                                 0
% 7.46/1.52  fd_pseudo                               0
% 7.46/1.52  fd_cond                                 0
% 7.46/1.52  fd_pseudo_cond                          1
% 7.46/1.52  AC symbols                              0
% 7.46/1.52  
% 7.46/1.52  ------ Schedule dynamic 5 is on 
% 7.46/1.52  
% 7.46/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  ------ 
% 7.46/1.52  Current options:
% 7.46/1.52  ------ 
% 7.46/1.52  
% 7.46/1.52  ------ Input Options
% 7.46/1.52  
% 7.46/1.52  --out_options                           all
% 7.46/1.52  --tptp_safe_out                         true
% 7.46/1.52  --problem_path                          ""
% 7.46/1.52  --include_path                          ""
% 7.46/1.52  --clausifier                            res/vclausify_rel
% 7.46/1.52  --clausifier_options                    ""
% 7.46/1.52  --stdin                                 false
% 7.46/1.52  --stats_out                             all
% 7.46/1.52  
% 7.46/1.52  ------ General Options
% 7.46/1.52  
% 7.46/1.52  --fof                                   false
% 7.46/1.52  --time_out_real                         305.
% 7.46/1.52  --time_out_virtual                      -1.
% 7.46/1.52  --symbol_type_check                     false
% 7.46/1.52  --clausify_out                          false
% 7.46/1.52  --sig_cnt_out                           false
% 7.46/1.52  --trig_cnt_out                          false
% 7.46/1.52  --trig_cnt_out_tolerance                1.
% 7.46/1.52  --trig_cnt_out_sk_spl                   false
% 7.46/1.52  --abstr_cl_out                          false
% 7.46/1.52  
% 7.46/1.52  ------ Global Options
% 7.46/1.52  
% 7.46/1.52  --schedule                              default
% 7.46/1.52  --add_important_lit                     false
% 7.46/1.52  --prop_solver_per_cl                    1000
% 7.46/1.52  --min_unsat_core                        false
% 7.46/1.52  --soft_assumptions                      false
% 7.46/1.52  --soft_lemma_size                       3
% 7.46/1.52  --prop_impl_unit_size                   0
% 7.46/1.52  --prop_impl_unit                        []
% 7.46/1.52  --share_sel_clauses                     true
% 7.46/1.52  --reset_solvers                         false
% 7.46/1.52  --bc_imp_inh                            [conj_cone]
% 7.46/1.52  --conj_cone_tolerance                   3.
% 7.46/1.52  --extra_neg_conj                        none
% 7.46/1.52  --large_theory_mode                     true
% 7.46/1.52  --prolific_symb_bound                   200
% 7.46/1.52  --lt_threshold                          2000
% 7.46/1.52  --clause_weak_htbl                      true
% 7.46/1.52  --gc_record_bc_elim                     false
% 7.46/1.52  
% 7.46/1.52  ------ Preprocessing Options
% 7.46/1.52  
% 7.46/1.52  --preprocessing_flag                    true
% 7.46/1.52  --time_out_prep_mult                    0.1
% 7.46/1.52  --splitting_mode                        input
% 7.46/1.52  --splitting_grd                         true
% 7.46/1.52  --splitting_cvd                         false
% 7.46/1.52  --splitting_cvd_svl                     false
% 7.46/1.52  --splitting_nvd                         32
% 7.46/1.52  --sub_typing                            true
% 7.46/1.52  --prep_gs_sim                           true
% 7.46/1.52  --prep_unflatten                        true
% 7.46/1.52  --prep_res_sim                          true
% 7.46/1.52  --prep_upred                            true
% 7.46/1.52  --prep_sem_filter                       exhaustive
% 7.46/1.52  --prep_sem_filter_out                   false
% 7.46/1.52  --pred_elim                             true
% 7.46/1.52  --res_sim_input                         true
% 7.46/1.52  --eq_ax_congr_red                       true
% 7.46/1.52  --pure_diseq_elim                       true
% 7.46/1.52  --brand_transform                       false
% 7.46/1.52  --non_eq_to_eq                          false
% 7.46/1.52  --prep_def_merge                        true
% 7.46/1.52  --prep_def_merge_prop_impl              false
% 7.46/1.52  --prep_def_merge_mbd                    true
% 7.46/1.52  --prep_def_merge_tr_red                 false
% 7.46/1.52  --prep_def_merge_tr_cl                  false
% 7.46/1.52  --smt_preprocessing                     true
% 7.46/1.52  --smt_ac_axioms                         fast
% 7.46/1.52  --preprocessed_out                      false
% 7.46/1.52  --preprocessed_stats                    false
% 7.46/1.52  
% 7.46/1.52  ------ Abstraction refinement Options
% 7.46/1.52  
% 7.46/1.52  --abstr_ref                             []
% 7.46/1.52  --abstr_ref_prep                        false
% 7.46/1.52  --abstr_ref_until_sat                   false
% 7.46/1.52  --abstr_ref_sig_restrict                funpre
% 7.46/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.46/1.52  --abstr_ref_under                       []
% 7.46/1.52  
% 7.46/1.52  ------ SAT Options
% 7.46/1.52  
% 7.46/1.52  --sat_mode                              false
% 7.46/1.52  --sat_fm_restart_options                ""
% 7.46/1.52  --sat_gr_def                            false
% 7.46/1.52  --sat_epr_types                         true
% 7.46/1.52  --sat_non_cyclic_types                  false
% 7.46/1.52  --sat_finite_models                     false
% 7.46/1.52  --sat_fm_lemmas                         false
% 7.46/1.52  --sat_fm_prep                           false
% 7.46/1.52  --sat_fm_uc_incr                        true
% 7.46/1.52  --sat_out_model                         small
% 7.46/1.52  --sat_out_clauses                       false
% 7.46/1.52  
% 7.46/1.52  ------ QBF Options
% 7.46/1.52  
% 7.46/1.52  --qbf_mode                              false
% 7.46/1.52  --qbf_elim_univ                         false
% 7.46/1.52  --qbf_dom_inst                          none
% 7.46/1.52  --qbf_dom_pre_inst                      false
% 7.46/1.52  --qbf_sk_in                             false
% 7.46/1.52  --qbf_pred_elim                         true
% 7.46/1.52  --qbf_split                             512
% 7.46/1.52  
% 7.46/1.52  ------ BMC1 Options
% 7.46/1.52  
% 7.46/1.52  --bmc1_incremental                      false
% 7.46/1.52  --bmc1_axioms                           reachable_all
% 7.46/1.52  --bmc1_min_bound                        0
% 7.46/1.52  --bmc1_max_bound                        -1
% 7.46/1.52  --bmc1_max_bound_default                -1
% 7.46/1.52  --bmc1_symbol_reachability              true
% 7.46/1.52  --bmc1_property_lemmas                  false
% 7.46/1.52  --bmc1_k_induction                      false
% 7.46/1.52  --bmc1_non_equiv_states                 false
% 7.46/1.52  --bmc1_deadlock                         false
% 7.46/1.52  --bmc1_ucm                              false
% 7.46/1.52  --bmc1_add_unsat_core                   none
% 7.46/1.52  --bmc1_unsat_core_children              false
% 7.46/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.46/1.52  --bmc1_out_stat                         full
% 7.46/1.52  --bmc1_ground_init                      false
% 7.46/1.52  --bmc1_pre_inst_next_state              false
% 7.46/1.52  --bmc1_pre_inst_state                   false
% 7.46/1.52  --bmc1_pre_inst_reach_state             false
% 7.46/1.52  --bmc1_out_unsat_core                   false
% 7.46/1.52  --bmc1_aig_witness_out                  false
% 7.46/1.52  --bmc1_verbose                          false
% 7.46/1.52  --bmc1_dump_clauses_tptp                false
% 7.46/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.46/1.52  --bmc1_dump_file                        -
% 7.46/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.46/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.46/1.52  --bmc1_ucm_extend_mode                  1
% 7.46/1.52  --bmc1_ucm_init_mode                    2
% 7.46/1.52  --bmc1_ucm_cone_mode                    none
% 7.46/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.46/1.52  --bmc1_ucm_relax_model                  4
% 7.46/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.46/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.46/1.52  --bmc1_ucm_layered_model                none
% 7.46/1.52  --bmc1_ucm_max_lemma_size               10
% 7.46/1.52  
% 7.46/1.52  ------ AIG Options
% 7.46/1.52  
% 7.46/1.52  --aig_mode                              false
% 7.46/1.52  
% 7.46/1.52  ------ Instantiation Options
% 7.46/1.52  
% 7.46/1.52  --instantiation_flag                    true
% 7.46/1.52  --inst_sos_flag                         true
% 7.46/1.52  --inst_sos_phase                        true
% 7.46/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.46/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.46/1.52  --inst_lit_sel_side                     none
% 7.46/1.52  --inst_solver_per_active                1400
% 7.46/1.52  --inst_solver_calls_frac                1.
% 7.46/1.52  --inst_passive_queue_type               priority_queues
% 7.46/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.46/1.52  --inst_passive_queues_freq              [25;2]
% 7.46/1.52  --inst_dismatching                      true
% 7.46/1.52  --inst_eager_unprocessed_to_passive     true
% 7.46/1.52  --inst_prop_sim_given                   true
% 7.46/1.52  --inst_prop_sim_new                     false
% 7.46/1.52  --inst_subs_new                         false
% 7.46/1.52  --inst_eq_res_simp                      false
% 7.46/1.52  --inst_subs_given                       false
% 7.46/1.52  --inst_orphan_elimination               true
% 7.46/1.52  --inst_learning_loop_flag               true
% 7.46/1.52  --inst_learning_start                   3000
% 7.46/1.52  --inst_learning_factor                  2
% 7.46/1.52  --inst_start_prop_sim_after_learn       3
% 7.46/1.52  --inst_sel_renew                        solver
% 7.46/1.52  --inst_lit_activity_flag                true
% 7.46/1.52  --inst_restr_to_given                   false
% 7.46/1.52  --inst_activity_threshold               500
% 7.46/1.52  --inst_out_proof                        true
% 7.46/1.52  
% 7.46/1.52  ------ Resolution Options
% 7.46/1.52  
% 7.46/1.52  --resolution_flag                       false
% 7.46/1.52  --res_lit_sel                           adaptive
% 7.46/1.52  --res_lit_sel_side                      none
% 7.46/1.52  --res_ordering                          kbo
% 7.46/1.52  --res_to_prop_solver                    active
% 7.46/1.52  --res_prop_simpl_new                    false
% 7.46/1.52  --res_prop_simpl_given                  true
% 7.46/1.52  --res_passive_queue_type                priority_queues
% 7.46/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.46/1.52  --res_passive_queues_freq               [15;5]
% 7.46/1.52  --res_forward_subs                      full
% 7.46/1.52  --res_backward_subs                     full
% 7.46/1.52  --res_forward_subs_resolution           true
% 7.46/1.52  --res_backward_subs_resolution          true
% 7.46/1.52  --res_orphan_elimination                true
% 7.46/1.52  --res_time_limit                        2.
% 7.46/1.52  --res_out_proof                         true
% 7.46/1.52  
% 7.46/1.52  ------ Superposition Options
% 7.46/1.52  
% 7.46/1.52  --superposition_flag                    true
% 7.46/1.52  --sup_passive_queue_type                priority_queues
% 7.46/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.46/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.46/1.52  --demod_completeness_check              fast
% 7.46/1.52  --demod_use_ground                      true
% 7.46/1.52  --sup_to_prop_solver                    passive
% 7.46/1.52  --sup_prop_simpl_new                    true
% 7.46/1.52  --sup_prop_simpl_given                  true
% 7.46/1.52  --sup_fun_splitting                     true
% 7.46/1.52  --sup_smt_interval                      50000
% 7.46/1.52  
% 7.46/1.52  ------ Superposition Simplification Setup
% 7.46/1.52  
% 7.46/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.46/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.46/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.46/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.46/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.46/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.46/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.46/1.52  --sup_immed_triv                        [TrivRules]
% 7.46/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.46/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.46/1.52  --sup_immed_bw_main                     []
% 7.46/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.46/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.46/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.46/1.52  --sup_input_bw                          []
% 7.46/1.52  
% 7.46/1.52  ------ Combination Options
% 7.46/1.52  
% 7.46/1.52  --comb_res_mult                         3
% 7.46/1.52  --comb_sup_mult                         2
% 7.46/1.52  --comb_inst_mult                        10
% 7.46/1.52  
% 7.46/1.52  ------ Debug Options
% 7.46/1.52  
% 7.46/1.52  --dbg_backtrace                         false
% 7.46/1.52  --dbg_dump_prop_clauses                 false
% 7.46/1.52  --dbg_dump_prop_clauses_file            -
% 7.46/1.52  --dbg_out_stat                          false
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  ------ Proving...
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  % SZS status Theorem for theBenchmark.p
% 7.46/1.52  
% 7.46/1.52   Resolution empty clause
% 7.46/1.52  
% 7.46/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.46/1.52  
% 7.46/1.52  fof(f1,axiom,(
% 7.46/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f29,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f1])).
% 7.46/1.52  
% 7.46/1.52  fof(f8,axiom,(
% 7.46/1.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f39,plain,(
% 7.46/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f8])).
% 7.46/1.52  
% 7.46/1.52  fof(f4,axiom,(
% 7.46/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f35,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.46/1.52    inference(cnf_transformation,[],[f4])).
% 7.46/1.52  
% 7.46/1.52  fof(f58,plain,(
% 7.46/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.46/1.52    inference(definition_unfolding,[],[f39,f35,f35])).
% 7.46/1.52  
% 7.46/1.52  fof(f7,axiom,(
% 7.46/1.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f38,plain,(
% 7.46/1.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.46/1.52    inference(cnf_transformation,[],[f7])).
% 7.46/1.52  
% 7.46/1.52  fof(f57,plain,(
% 7.46/1.52    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 7.46/1.52    inference(definition_unfolding,[],[f38,f35])).
% 7.46/1.52  
% 7.46/1.52  fof(f10,axiom,(
% 7.46/1.52    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f41,plain,(
% 7.46/1.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f10])).
% 7.46/1.52  
% 7.46/1.52  fof(f9,axiom,(
% 7.46/1.52    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f40,plain,(
% 7.46/1.52    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.46/1.52    inference(cnf_transformation,[],[f9])).
% 7.46/1.52  
% 7.46/1.52  fof(f59,plain,(
% 7.46/1.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 7.46/1.52    inference(definition_unfolding,[],[f40,f35])).
% 7.46/1.52  
% 7.46/1.52  fof(f16,axiom,(
% 7.46/1.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f20,plain,(
% 7.46/1.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 7.46/1.52    inference(unused_predicate_definition_removal,[],[f16])).
% 7.46/1.52  
% 7.46/1.52  fof(f22,plain,(
% 7.46/1.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 7.46/1.52    inference(ennf_transformation,[],[f20])).
% 7.46/1.52  
% 7.46/1.52  fof(f47,plain,(
% 7.46/1.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f22])).
% 7.46/1.52  
% 7.46/1.52  fof(f12,axiom,(
% 7.46/1.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f43,plain,(
% 7.46/1.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f12])).
% 7.46/1.52  
% 7.46/1.52  fof(f13,axiom,(
% 7.46/1.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f44,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f13])).
% 7.46/1.52  
% 7.46/1.52  fof(f14,axiom,(
% 7.46/1.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f45,plain,(
% 7.46/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f14])).
% 7.46/1.52  
% 7.46/1.52  fof(f15,axiom,(
% 7.46/1.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f46,plain,(
% 7.46/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f15])).
% 7.46/1.52  
% 7.46/1.52  fof(f51,plain,(
% 7.46/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.46/1.52    inference(definition_unfolding,[],[f45,f46])).
% 7.46/1.52  
% 7.46/1.52  fof(f52,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.46/1.52    inference(definition_unfolding,[],[f44,f51])).
% 7.46/1.52  
% 7.46/1.52  fof(f53,plain,(
% 7.46/1.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.46/1.52    inference(definition_unfolding,[],[f43,f52])).
% 7.46/1.52  
% 7.46/1.52  fof(f60,plain,(
% 7.46/1.52    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.46/1.52    inference(definition_unfolding,[],[f47,f53])).
% 7.46/1.52  
% 7.46/1.52  fof(f18,conjecture,(
% 7.46/1.52    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f19,negated_conjecture,(
% 7.46/1.52    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.46/1.52    inference(negated_conjecture,[],[f18])).
% 7.46/1.52  
% 7.46/1.52  fof(f23,plain,(
% 7.46/1.52    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 7.46/1.52    inference(ennf_transformation,[],[f19])).
% 7.46/1.52  
% 7.46/1.52  fof(f27,plain,(
% 7.46/1.52    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 7.46/1.52    introduced(choice_axiom,[])).
% 7.46/1.52  
% 7.46/1.52  fof(f28,plain,(
% 7.46/1.52    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 7.46/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).
% 7.46/1.52  
% 7.46/1.52  fof(f49,plain,(
% 7.46/1.52    r2_hidden(sK0,sK1)),
% 7.46/1.52    inference(cnf_transformation,[],[f28])).
% 7.46/1.52  
% 7.46/1.52  fof(f5,axiom,(
% 7.46/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f21,plain,(
% 7.46/1.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.46/1.52    inference(ennf_transformation,[],[f5])).
% 7.46/1.52  
% 7.46/1.52  fof(f36,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f21])).
% 7.46/1.52  
% 7.46/1.52  fof(f6,axiom,(
% 7.46/1.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f37,plain,(
% 7.46/1.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f6])).
% 7.46/1.52  
% 7.46/1.52  fof(f56,plain,(
% 7.46/1.52    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.46/1.52    inference(definition_unfolding,[],[f37,f35])).
% 7.46/1.52  
% 7.46/1.52  fof(f2,axiom,(
% 7.46/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f24,plain,(
% 7.46/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.46/1.52    inference(nnf_transformation,[],[f2])).
% 7.46/1.52  
% 7.46/1.52  fof(f25,plain,(
% 7.46/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.46/1.52    inference(flattening,[],[f24])).
% 7.46/1.52  
% 7.46/1.52  fof(f30,plain,(
% 7.46/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.46/1.52    inference(cnf_transformation,[],[f25])).
% 7.46/1.52  
% 7.46/1.52  fof(f64,plain,(
% 7.46/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.46/1.52    inference(equality_resolution,[],[f30])).
% 7.46/1.52  
% 7.46/1.52  fof(f3,axiom,(
% 7.46/1.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f26,plain,(
% 7.46/1.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.46/1.52    inference(nnf_transformation,[],[f3])).
% 7.46/1.52  
% 7.46/1.52  fof(f34,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f26])).
% 7.46/1.52  
% 7.46/1.52  fof(f54,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 7.46/1.52    inference(definition_unfolding,[],[f34,f35])).
% 7.46/1.52  
% 7.46/1.52  fof(f50,plain,(
% 7.46/1.52    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 7.46/1.52    inference(cnf_transformation,[],[f28])).
% 7.46/1.52  
% 7.46/1.52  fof(f11,axiom,(
% 7.46/1.52    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.46/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.52  
% 7.46/1.52  fof(f42,plain,(
% 7.46/1.52    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.46/1.52    inference(cnf_transformation,[],[f11])).
% 7.46/1.52  
% 7.46/1.52  fof(f62,plain,(
% 7.46/1.52    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1),
% 7.46/1.52    inference(definition_unfolding,[],[f50,f42,f35,f53,f53])).
% 7.46/1.52  
% 7.46/1.52  fof(f33,plain,(
% 7.46/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.46/1.52    inference(cnf_transformation,[],[f26])).
% 7.46/1.52  
% 7.46/1.52  fof(f55,plain,(
% 7.46/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.46/1.52    inference(definition_unfolding,[],[f33,f35])).
% 7.46/1.52  
% 7.46/1.52  cnf(c_0,plain,
% 7.46/1.52      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.46/1.52      inference(cnf_transformation,[],[f29]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_9,plain,
% 7.46/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.46/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_8,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.46/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_11,plain,
% 7.46/1.52      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.46/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_805,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_8,c_11]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1197,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_9,c_805]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_10,plain,
% 7.46/1.52      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.46/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1210,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = X0 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_1197,c_8,c_10]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1298,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_0,c_1210]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1520,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1298,c_805]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1521,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_1520,c_8]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_5294,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1521,c_805]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_5304,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0),k1_xboole_0))) = X0 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_5294,c_8]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_12,plain,
% 7.46/1.52      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 7.46/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_15,negated_conjecture,
% 7.46/1.52      ( r2_hidden(sK0,sK1) ),
% 7.46/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_142,plain,
% 7.46/1.52      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | sK0 != X0 | sK1 != X1 ),
% 7.46/1.52      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_143,plain,
% 7.46/1.52      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 7.46/1.52      inference(unflattening,[status(thm)],[c_142]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_428,plain,
% 7.46/1.52      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 7.46/1.52      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_6,plain,
% 7.46/1.52      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.46/1.52      inference(cnf_transformation,[],[f36]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_430,plain,
% 7.46/1.52      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.46/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1412,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_428,c_430]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1738,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1412,c_9]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_7,plain,
% 7.46/1.52      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.46/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_429,plain,
% 7.46/1.52      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.46/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_808,plain,
% 7.46/1.52      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2))),k5_xboole_0(X0,X1)) = iProver_top ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_11,c_429]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_3992,plain,
% 7.46/1.52      ( r1_tarski(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),X1))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1738,c_808]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1975,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X1)) = k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),X1) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1738,c_11]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4019,plain,
% 7.46/1.52      ( r1_tarski(k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),X1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_3992,c_1975]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_938,plain,
% 7.46/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4020,plain,
% 7.46/1.52      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X1))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_4019,c_938]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4021,plain,
% 7.46/1.52      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_4020,c_1738]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4924,plain,
% 7.46/1.52      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_8,c_4021]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4946,plain,
% 7.46/1.52      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = iProver_top ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_4924,c_1412]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_5090,plain,
% 7.46/1.52      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_4946,c_430]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_11221,plain,
% 7.46/1.52      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_5304,c_5090]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_11285,plain,
% 7.46/1.52      ( k3_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_11221,c_5304]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1743,plain,
% 7.46/1.52      ( k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1412,c_0]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_11286,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_11285,c_1412,c_1743]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1969,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_0,c_1738]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_11749,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_11286,c_1969]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4801,plain,
% 7.46/1.52      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X1)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_9,c_1975]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4837,plain,
% 7.46/1.52      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X1)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_4801,c_1738]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_6236,plain,
% 7.46/1.52      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1412,c_4837]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f64]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_433,plain,
% 7.46/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.46/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1410,plain,
% 7.46/1.52      ( k3_xboole_0(X0,X0) = X0 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_433,c_430]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4,plain,
% 7.46/1.52      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.46/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_432,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 7.46/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.46/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2860,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_433,c_432]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2877,plain,
% 7.46/1.52      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_2860,c_1410]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2863,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_428,c_432]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1971,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1412,c_1738]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1981,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)) ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_1971,c_1410]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2874,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)) = k1_xboole_0 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_2863,c_1412,c_1981]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2878,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k1_xboole_0 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_2877,c_2874]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_6263,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_6236,c_1410,c_2877,c_2878]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_7312,plain,
% 7.46/1.52      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_6263,c_4946]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_7903,plain,
% 7.46/1.52      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = iProver_top ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1412,c_7312]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_7912,plain,
% 7.46/1.52      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = iProver_top ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_7903,c_8,c_1410,c_1743,c_2877]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_8689,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_7912,c_432]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_8690,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_7912,c_430]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_8691,plain,
% 7.46/1.52      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_8689,c_8690]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_11753,plain,
% 7.46/1.52      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_11749,c_1743,c_8691]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_14,negated_conjecture,
% 7.46/1.52      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 7.46/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_572,plain,
% 7.46/1.52      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_0,c_14]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_802,plain,
% 7.46/1.52      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_11,c_572]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1040,plain,
% 7.46/1.52      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) != sK1 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_11,c_802]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1850,plain,
% 7.46/1.52      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_1743,c_1040]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2053,plain,
% 7.46/1.52      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_1850,c_1981]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_13013,plain,
% 7.46/1.52      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)),k1_xboole_0)) != sK1 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_11753,c_2053]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_657,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1198,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_657,c_805]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1209,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_1198,c_8]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1290,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_1209,c_805]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_1291,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
% 7.46/1.52      inference(light_normalisation,[status(thm)],[c_1290,c_8]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_5,plain,
% 7.46/1.52      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.46/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_431,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.46/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.46/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2174,plain,
% 7.46/1.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_10,c_431]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_2210,plain,
% 7.46/1.52      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.46/1.52      inference(superposition,[status(thm)],[c_2174,c_430]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_4224,plain,
% 7.46/1.52      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_1291,c_2210]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_13014,plain,
% 7.46/1.52      ( k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1))) != sK1 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_13013,c_4224]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_13015,plain,
% 7.46/1.52      ( sK1 != sK1 ),
% 7.46/1.52      inference(demodulation,[status(thm)],[c_13014,c_2877,c_2878,c_4224]) ).
% 7.46/1.52  
% 7.46/1.52  cnf(c_13016,plain,
% 7.46/1.52      ( $false ),
% 7.46/1.52      inference(equality_resolution_simp,[status(thm)],[c_13015]) ).
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.46/1.52  
% 7.46/1.52  ------                               Statistics
% 7.46/1.52  
% 7.46/1.52  ------ General
% 7.46/1.52  
% 7.46/1.52  abstr_ref_over_cycles:                  0
% 7.46/1.52  abstr_ref_under_cycles:                 0
% 7.46/1.52  gc_basic_clause_elim:                   0
% 7.46/1.52  forced_gc_time:                         0
% 7.46/1.52  parsing_time:                           0.024
% 7.46/1.52  unif_index_cands_time:                  0.
% 7.46/1.52  unif_index_add_time:                    0.
% 7.46/1.52  orderings_time:                         0.
% 7.46/1.52  out_proof_time:                         0.008
% 7.46/1.52  total_time:                             0.52
% 7.46/1.52  num_of_symbols:                         40
% 7.46/1.52  num_of_terms:                           18413
% 7.46/1.52  
% 7.46/1.52  ------ Preprocessing
% 7.46/1.52  
% 7.46/1.52  num_of_splits:                          0
% 7.46/1.52  num_of_split_atoms:                     0
% 7.46/1.52  num_of_reused_defs:                     0
% 7.46/1.52  num_eq_ax_congr_red:                    1
% 7.46/1.52  num_of_sem_filtered_clauses:            1
% 7.46/1.52  num_of_subtypes:                        0
% 7.46/1.52  monotx_restored_types:                  0
% 7.46/1.52  sat_num_of_epr_types:                   0
% 7.46/1.52  sat_num_of_non_cyclic_types:            0
% 7.46/1.52  sat_guarded_non_collapsed_types:        0
% 7.46/1.52  num_pure_diseq_elim:                    0
% 7.46/1.52  simp_replaced_by:                       0
% 7.46/1.52  res_preprocessed:                       72
% 7.46/1.52  prep_upred:                             0
% 7.46/1.52  prep_unflattend:                        2
% 7.46/1.52  smt_new_axioms:                         0
% 7.46/1.52  pred_elim_cands:                        1
% 7.46/1.52  pred_elim:                              1
% 7.46/1.52  pred_elim_cl:                           1
% 7.46/1.52  pred_elim_cycles:                       3
% 7.46/1.52  merged_defs:                            8
% 7.46/1.52  merged_defs_ncl:                        0
% 7.46/1.52  bin_hyper_res:                          8
% 7.46/1.52  prep_cycles:                            4
% 7.46/1.52  pred_elim_time:                         0.
% 7.46/1.52  splitting_time:                         0.
% 7.46/1.52  sem_filter_time:                        0.
% 7.46/1.52  monotx_time:                            0.
% 7.46/1.52  subtype_inf_time:                       0.
% 7.46/1.52  
% 7.46/1.52  ------ Problem properties
% 7.46/1.52  
% 7.46/1.52  clauses:                                14
% 7.46/1.52  conjectures:                            1
% 7.46/1.52  epr:                                    2
% 7.46/1.52  horn:                                   14
% 7.46/1.52  ground:                                 2
% 7.46/1.52  unary:                                  10
% 7.46/1.52  binary:                                 3
% 7.46/1.52  lits:                                   19
% 7.46/1.52  lits_eq:                                11
% 7.46/1.52  fd_pure:                                0
% 7.46/1.52  fd_pseudo:                              0
% 7.46/1.52  fd_cond:                                0
% 7.46/1.52  fd_pseudo_cond:                         1
% 7.46/1.52  ac_symbols:                             0
% 7.46/1.52  
% 7.46/1.52  ------ Propositional Solver
% 7.46/1.52  
% 7.46/1.52  prop_solver_calls:                      36
% 7.46/1.52  prop_fast_solver_calls:                 416
% 7.46/1.52  smt_solver_calls:                       0
% 7.46/1.52  smt_fast_solver_calls:                  0
% 7.46/1.52  prop_num_of_clauses:                    5501
% 7.46/1.52  prop_preprocess_simplified:             9141
% 7.46/1.52  prop_fo_subsumed:                       0
% 7.46/1.52  prop_solver_time:                       0.
% 7.46/1.52  smt_solver_time:                        0.
% 7.46/1.52  smt_fast_solver_time:                   0.
% 7.46/1.52  prop_fast_solver_time:                  0.
% 7.46/1.52  prop_unsat_core_time:                   0.
% 7.46/1.52  
% 7.46/1.52  ------ QBF
% 7.46/1.52  
% 7.46/1.52  qbf_q_res:                              0
% 7.46/1.52  qbf_num_tautologies:                    0
% 7.46/1.52  qbf_prep_cycles:                        0
% 7.46/1.52  
% 7.46/1.52  ------ BMC1
% 7.46/1.52  
% 7.46/1.52  bmc1_current_bound:                     -1
% 7.46/1.52  bmc1_last_solved_bound:                 -1
% 7.46/1.52  bmc1_unsat_core_size:                   -1
% 7.46/1.52  bmc1_unsat_core_parents_size:           -1
% 7.46/1.52  bmc1_merge_next_fun:                    0
% 7.46/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.46/1.52  
% 7.46/1.52  ------ Instantiation
% 7.46/1.52  
% 7.46/1.52  inst_num_of_clauses:                    1504
% 7.46/1.52  inst_num_in_passive:                    714
% 7.46/1.52  inst_num_in_active:                     651
% 7.46/1.52  inst_num_in_unprocessed:                139
% 7.46/1.52  inst_num_of_loops:                      680
% 7.46/1.52  inst_num_of_learning_restarts:          0
% 7.46/1.52  inst_num_moves_active_passive:          23
% 7.46/1.52  inst_lit_activity:                      0
% 7.46/1.52  inst_lit_activity_moves:                0
% 7.46/1.52  inst_num_tautologies:                   0
% 7.46/1.52  inst_num_prop_implied:                  0
% 7.46/1.52  inst_num_existing_simplified:           0
% 7.46/1.52  inst_num_eq_res_simplified:             0
% 7.46/1.52  inst_num_child_elim:                    0
% 7.46/1.52  inst_num_of_dismatching_blockings:      877
% 7.46/1.52  inst_num_of_non_proper_insts:           2055
% 7.46/1.52  inst_num_of_duplicates:                 0
% 7.46/1.52  inst_inst_num_from_inst_to_res:         0
% 7.46/1.52  inst_dismatching_checking_time:         0.
% 7.46/1.52  
% 7.46/1.52  ------ Resolution
% 7.46/1.52  
% 7.46/1.52  res_num_of_clauses:                     0
% 7.46/1.52  res_num_in_passive:                     0
% 7.46/1.52  res_num_in_active:                      0
% 7.46/1.52  res_num_of_loops:                       76
% 7.46/1.52  res_forward_subset_subsumed:            271
% 7.46/1.52  res_backward_subset_subsumed:           2
% 7.46/1.52  res_forward_subsumed:                   0
% 7.46/1.52  res_backward_subsumed:                  0
% 7.46/1.52  res_forward_subsumption_resolution:     0
% 7.46/1.52  res_backward_subsumption_resolution:    0
% 7.46/1.52  res_clause_to_clause_subsumption:       3883
% 7.46/1.52  res_orphan_elimination:                 0
% 7.46/1.52  res_tautology_del:                      150
% 7.46/1.52  res_num_eq_res_simplified:              0
% 7.46/1.52  res_num_sel_changes:                    0
% 7.46/1.52  res_moves_from_active_to_pass:          0
% 7.46/1.52  
% 7.46/1.52  ------ Superposition
% 7.46/1.52  
% 7.46/1.52  sup_time_total:                         0.
% 7.46/1.52  sup_time_generating:                    0.
% 7.46/1.52  sup_time_sim_full:                      0.
% 7.46/1.52  sup_time_sim_immed:                     0.
% 7.46/1.52  
% 7.46/1.52  sup_num_of_clauses:                     726
% 7.46/1.52  sup_num_in_active:                      109
% 7.46/1.52  sup_num_in_passive:                     617
% 7.46/1.52  sup_num_of_loops:                       134
% 7.46/1.52  sup_fw_superposition:                   1498
% 7.46/1.52  sup_bw_superposition:                   903
% 7.46/1.52  sup_immediate_simplified:               1148
% 7.46/1.52  sup_given_eliminated:                   2
% 7.46/1.52  comparisons_done:                       0
% 7.46/1.52  comparisons_avoided:                    0
% 7.46/1.52  
% 7.46/1.52  ------ Simplifications
% 7.46/1.52  
% 7.46/1.52  
% 7.46/1.52  sim_fw_subset_subsumed:                 3
% 7.46/1.52  sim_bw_subset_subsumed:                 0
% 7.46/1.52  sim_fw_subsumed:                        186
% 7.46/1.52  sim_bw_subsumed:                        20
% 7.46/1.52  sim_fw_subsumption_res:                 0
% 7.46/1.52  sim_bw_subsumption_res:                 0
% 7.46/1.52  sim_tautology_del:                      0
% 7.46/1.52  sim_eq_tautology_del:                   294
% 7.46/1.52  sim_eq_res_simp:                        6
% 7.46/1.52  sim_fw_demodulated:                     771
% 7.46/1.52  sim_bw_demodulated:                     24
% 7.46/1.52  sim_light_normalised:                   499
% 7.46/1.52  sim_joinable_taut:                      0
% 7.46/1.52  sim_joinable_simp:                      0
% 7.46/1.52  sim_ac_normalised:                      0
% 7.46/1.52  sim_smt_subsumption:                    0
% 7.46/1.52  
%------------------------------------------------------------------------------
