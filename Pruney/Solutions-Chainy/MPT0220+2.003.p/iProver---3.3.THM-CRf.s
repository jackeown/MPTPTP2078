%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:28 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 271 expanded)
%              Number of clauses        :   50 (  75 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 ( 391 expanded)
%              Number of equality atoms :  104 ( 239 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f69])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f74,f73])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f24,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f24])).

fof(f32,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f25])).

fof(f39,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39])).

fof(f67,plain,(
    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f58,f49])).

fof(f79,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f67,f68,f74,f73,f73])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f55,f49])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f33])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f35])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f53,f49])).

cnf(c_16,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_410,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_416,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1717,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_410,c_416])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_572,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_17])).

cnf(c_31969,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1717,c_572])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_417,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1714,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_417,c_416])).

cnf(c_13,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_412,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_990,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_412])).

cnf(c_2283,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_990])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_421,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_420,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3654,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_420])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_415,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1715,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_415,c_416])).

cnf(c_2324,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1715,c_0])).

cnf(c_13659,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_3654])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13954,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13659,c_28])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_411,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13959,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13954,c_411])).

cnf(c_14066,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3654,c_13959])).

cnf(c_14279,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2283,c_14066])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_414,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1124,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_414])).

cnf(c_2282,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1124])).

cnf(c_2858,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2282,c_416])).

cnf(c_14339,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14279,c_2858])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_486,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_15,c_1])).

cnf(c_14711,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14339,c_486])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_677,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_2310,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1715,c_677])).

cnf(c_14722,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_14711,c_2310])).

cnf(c_31970,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_31969,c_14722])).

cnf(c_31971,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_31970])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:20:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.66/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.66/1.98  
% 11.66/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.66/1.98  
% 11.66/1.98  ------  iProver source info
% 11.66/1.98  
% 11.66/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.66/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.66/1.98  git: non_committed_changes: false
% 11.66/1.98  git: last_make_outside_of_git: false
% 11.66/1.98  
% 11.66/1.98  ------ 
% 11.66/1.98  ------ Parsing...
% 11.66/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.66/1.98  
% 11.66/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.66/1.98  
% 11.66/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.66/1.98  
% 11.66/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.66/1.98  ------ Proving...
% 11.66/1.98  ------ Problem Properties 
% 11.66/1.98  
% 11.66/1.98  
% 11.66/1.98  clauses                                 17
% 11.66/1.98  conjectures                             1
% 11.66/1.98  EPR                                     5
% 11.66/1.98  Horn                                    15
% 11.66/1.98  unary                                   11
% 11.66/1.98  binary                                  4
% 11.66/1.98  lits                                    25
% 11.66/1.98  lits eq                                 8
% 11.66/1.98  fd_pure                                 0
% 11.66/1.98  fd_pseudo                               0
% 11.66/1.98  fd_cond                                 0
% 11.66/1.98  fd_pseudo_cond                          2
% 11.66/1.98  AC symbols                              1
% 11.66/1.98  
% 11.66/1.98  ------ Input Options Time Limit: Unbounded
% 11.66/1.98  
% 11.66/1.98  
% 11.66/1.98  ------ 
% 11.66/1.98  Current options:
% 11.66/1.98  ------ 
% 11.66/1.98  
% 11.66/1.98  
% 11.66/1.98  
% 11.66/1.98  
% 11.66/1.98  ------ Proving...
% 11.66/1.98  
% 11.66/1.98  
% 11.66/1.98  % SZS status Theorem for theBenchmark.p
% 11.66/1.98  
% 11.66/1.98   Resolution empty clause
% 11.66/1.98  
% 11.66/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.66/1.98  
% 11.66/1.98  fof(f23,axiom,(
% 11.66/1.98    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f66,plain,(
% 11.66/1.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 11.66/1.98    inference(cnf_transformation,[],[f23])).
% 11.66/1.98  
% 11.66/1.98  fof(f16,axiom,(
% 11.66/1.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f59,plain,(
% 11.66/1.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f16])).
% 11.66/1.98  
% 11.66/1.98  fof(f74,plain,(
% 11.66/1.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f59,f73])).
% 11.66/1.98  
% 11.66/1.98  fof(f17,axiom,(
% 11.66/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f60,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f17])).
% 11.66/1.98  
% 11.66/1.98  fof(f18,axiom,(
% 11.66/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f61,plain,(
% 11.66/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f18])).
% 11.66/1.98  
% 11.66/1.98  fof(f19,axiom,(
% 11.66/1.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f62,plain,(
% 11.66/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f19])).
% 11.66/1.98  
% 11.66/1.98  fof(f20,axiom,(
% 11.66/1.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f63,plain,(
% 11.66/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f20])).
% 11.66/1.98  
% 11.66/1.98  fof(f21,axiom,(
% 11.66/1.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f64,plain,(
% 11.66/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f21])).
% 11.66/1.98  
% 11.66/1.98  fof(f22,axiom,(
% 11.66/1.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f65,plain,(
% 11.66/1.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f22])).
% 11.66/1.98  
% 11.66/1.98  fof(f69,plain,(
% 11.66/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f64,f65])).
% 11.66/1.98  
% 11.66/1.98  fof(f70,plain,(
% 11.66/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f63,f69])).
% 11.66/1.98  
% 11.66/1.98  fof(f71,plain,(
% 11.66/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f62,f70])).
% 11.66/1.98  
% 11.66/1.98  fof(f72,plain,(
% 11.66/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f61,f71])).
% 11.66/1.98  
% 11.66/1.98  fof(f73,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f60,f72])).
% 11.66/1.98  
% 11.66/1.98  fof(f78,plain,(
% 11.66/1.98    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.66/1.98    inference(definition_unfolding,[],[f66,f74,f73])).
% 11.66/1.98  
% 11.66/1.98  fof(f7,axiom,(
% 11.66/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f30,plain,(
% 11.66/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.66/1.98    inference(ennf_transformation,[],[f7])).
% 11.66/1.98  
% 11.66/1.98  fof(f50,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f30])).
% 11.66/1.98  
% 11.66/1.98  fof(f1,axiom,(
% 11.66/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f41,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f1])).
% 11.66/1.98  
% 11.66/1.98  fof(f24,conjecture,(
% 11.66/1.98    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f25,negated_conjecture,(
% 11.66/1.98    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 11.66/1.98    inference(negated_conjecture,[],[f24])).
% 11.66/1.98  
% 11.66/1.98  fof(f32,plain,(
% 11.66/1.98    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 11.66/1.98    inference(ennf_transformation,[],[f25])).
% 11.66/1.98  
% 11.66/1.98  fof(f39,plain,(
% 11.66/1.98    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3)),
% 11.66/1.98    introduced(choice_axiom,[])).
% 11.66/1.98  
% 11.66/1.98  fof(f40,plain,(
% 11.66/1.98    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3)),
% 11.66/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39])).
% 11.66/1.98  
% 11.66/1.98  fof(f67,plain,(
% 11.66/1.98    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3)),
% 11.66/1.98    inference(cnf_transformation,[],[f40])).
% 11.66/1.98  
% 11.66/1.98  fof(f15,axiom,(
% 11.66/1.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f58,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f15])).
% 11.66/1.98  
% 11.66/1.98  fof(f6,axiom,(
% 11.66/1.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f49,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f6])).
% 11.66/1.98  
% 11.66/1.98  fof(f68,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f58,f49])).
% 11.66/1.98  
% 11.66/1.98  fof(f79,plain,(
% 11.66/1.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 11.66/1.98    inference(definition_unfolding,[],[f67,f68,f74,f73,f73])).
% 11.66/1.98  
% 11.66/1.98  fof(f5,axiom,(
% 11.66/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f37,plain,(
% 11.66/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.66/1.98    inference(nnf_transformation,[],[f5])).
% 11.66/1.98  
% 11.66/1.98  fof(f38,plain,(
% 11.66/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.66/1.98    inference(flattening,[],[f37])).
% 11.66/1.98  
% 11.66/1.98  fof(f46,plain,(
% 11.66/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.66/1.98    inference(cnf_transformation,[],[f38])).
% 11.66/1.98  
% 11.66/1.98  fof(f81,plain,(
% 11.66/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.66/1.98    inference(equality_resolution,[],[f46])).
% 11.66/1.98  
% 11.66/1.98  fof(f12,axiom,(
% 11.66/1.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f55,plain,(
% 11.66/1.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f12])).
% 11.66/1.98  
% 11.66/1.98  fof(f77,plain,(
% 11.66/1.98    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f55,f49])).
% 11.66/1.98  
% 11.66/1.98  fof(f3,axiom,(
% 11.66/1.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f27,plain,(
% 11.66/1.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 11.66/1.98    inference(unused_predicate_definition_removal,[],[f3])).
% 11.66/1.98  
% 11.66/1.98  fof(f28,plain,(
% 11.66/1.98    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 11.66/1.98    inference(ennf_transformation,[],[f27])).
% 11.66/1.98  
% 11.66/1.98  fof(f33,plain,(
% 11.66/1.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.66/1.98    introduced(choice_axiom,[])).
% 11.66/1.98  
% 11.66/1.98  fof(f34,plain,(
% 11.66/1.98    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 11.66/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f33])).
% 11.66/1.98  
% 11.66/1.98  fof(f43,plain,(
% 11.66/1.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f34])).
% 11.66/1.98  
% 11.66/1.98  fof(f4,axiom,(
% 11.66/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f26,plain,(
% 11.66/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.66/1.98    inference(rectify,[],[f4])).
% 11.66/1.98  
% 11.66/1.98  fof(f29,plain,(
% 11.66/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.66/1.98    inference(ennf_transformation,[],[f26])).
% 11.66/1.98  
% 11.66/1.98  fof(f35,plain,(
% 11.66/1.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 11.66/1.98    introduced(choice_axiom,[])).
% 11.66/1.98  
% 11.66/1.98  fof(f36,plain,(
% 11.66/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.66/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f35])).
% 11.66/1.98  
% 11.66/1.98  fof(f45,plain,(
% 11.66/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.66/1.98    inference(cnf_transformation,[],[f36])).
% 11.66/1.98  
% 11.66/1.98  fof(f8,axiom,(
% 11.66/1.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f51,plain,(
% 11.66/1.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f8])).
% 11.66/1.98  
% 11.66/1.98  fof(f11,axiom,(
% 11.66/1.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f54,plain,(
% 11.66/1.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f11])).
% 11.66/1.98  
% 11.66/1.98  fof(f13,axiom,(
% 11.66/1.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f31,plain,(
% 11.66/1.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 11.66/1.98    inference(ennf_transformation,[],[f13])).
% 11.66/1.98  
% 11.66/1.98  fof(f56,plain,(
% 11.66/1.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f31])).
% 11.66/1.98  
% 11.66/1.98  fof(f9,axiom,(
% 11.66/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f52,plain,(
% 11.66/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f9])).
% 11.66/1.98  
% 11.66/1.98  fof(f75,plain,(
% 11.66/1.98    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.66/1.98    inference(definition_unfolding,[],[f52,f49])).
% 11.66/1.98  
% 11.66/1.98  fof(f14,axiom,(
% 11.66/1.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f57,plain,(
% 11.66/1.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f14])).
% 11.66/1.98  
% 11.66/1.98  fof(f2,axiom,(
% 11.66/1.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f42,plain,(
% 11.66/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.66/1.98    inference(cnf_transformation,[],[f2])).
% 11.66/1.98  
% 11.66/1.98  fof(f10,axiom,(
% 11.66/1.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.66/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.98  
% 11.66/1.98  fof(f53,plain,(
% 11.66/1.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.66/1.98    inference(cnf_transformation,[],[f10])).
% 11.66/1.98  
% 11.66/1.98  fof(f76,plain,(
% 11.66/1.98    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 11.66/1.98    inference(definition_unfolding,[],[f53,f49])).
% 11.66/1.98  
% 11.66/1.98  cnf(c_16,plain,
% 11.66/1.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 11.66/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_410,plain,
% 11.66/1.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_8,plain,
% 11.66/1.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.66/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_416,plain,
% 11.66/1.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_1717,plain,
% 11.66/1.98      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_410,c_416]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_0,plain,
% 11.66/1.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.66/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_17,negated_conjecture,
% 11.66/1.98      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 11.66/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_572,plain,
% 11.66/1.98      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 11.66/1.98      inference(demodulation,[status(thm)],[c_0,c_17]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_31969,plain,
% 11.66/1.98      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 11.66/1.98      inference(demodulation,[status(thm)],[c_1717,c_572]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f81]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_417,plain,
% 11.66/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_1714,plain,
% 11.66/1.98      ( k3_xboole_0(X0,X0) = X0 ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_417,c_416]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_13,plain,
% 11.66/1.98      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 11.66/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_412,plain,
% 11.66/1.98      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_990,plain,
% 11.66/1.98      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_0,c_412]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_2283,plain,
% 11.66/1.98      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_1714,c_990]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_2,plain,
% 11.66/1.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 11.66/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_421,plain,
% 11.66/1.98      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_3,plain,
% 11.66/1.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 11.66/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_420,plain,
% 11.66/1.98      ( r1_xboole_0(X0,X1) != iProver_top
% 11.66/1.98      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_3654,plain,
% 11.66/1.98      ( r1_xboole_0(X0,X1) != iProver_top
% 11.66/1.98      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_421,c_420]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_9,plain,
% 11.66/1.98      ( r1_tarski(k1_xboole_0,X0) ),
% 11.66/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_415,plain,
% 11.66/1.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_1715,plain,
% 11.66/1.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_415,c_416]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_2324,plain,
% 11.66/1.98      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_1715,c_0]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_13659,plain,
% 11.66/1.98      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 11.66/1.98      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_2324,c_3654]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_12,plain,
% 11.66/1.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.66/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_28,plain,
% 11.66/1.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_13954,plain,
% 11.66/1.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.66/1.98      inference(global_propositional_subsumption,[status(thm)],[c_13659,c_28]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_14,plain,
% 11.66/1.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 11.66/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_411,plain,
% 11.66/1.98      ( X0 = X1
% 11.66/1.98      | v1_xboole_0(X0) != iProver_top
% 11.66/1.98      | v1_xboole_0(X1) != iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_13959,plain,
% 11.66/1.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_13954,c_411]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_14066,plain,
% 11.66/1.98      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_3654,c_13959]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_14279,plain,
% 11.66/1.98      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k1_xboole_0 ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_2283,c_14066]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_10,plain,
% 11.66/1.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.66/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_414,plain,
% 11.66/1.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.66/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_1124,plain,
% 11.66/1.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_0,c_414]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_2282,plain,
% 11.66/1.98      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_1714,c_1124]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_2858,plain,
% 11.66/1.98      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_2282,c_416]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_14339,plain,
% 11.66/1.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.66/1.98      inference(demodulation,[status(thm)],[c_14279,c_2858]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_15,plain,
% 11.66/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.66/1.98      inference(cnf_transformation,[],[f57]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_1,plain,
% 11.66/1.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.66/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_486,plain,
% 11.66/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_15,c_1]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_14711,plain,
% 11.66/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_14339,c_486]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_11,plain,
% 11.66/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.66/1.98      inference(cnf_transformation,[],[f76]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_677,plain,
% 11.66/1.98      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.66/1.98      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_2310,plain,
% 11.66/1.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.66/1.98      inference(demodulation,[status(thm)],[c_1715,c_677]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_14722,plain,
% 11.66/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.66/1.98      inference(demodulation,[status(thm)],[c_14711,c_2310]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_31970,plain,
% 11.66/1.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 11.66/1.98      inference(demodulation,[status(thm)],[c_31969,c_14722]) ).
% 11.66/1.98  
% 11.66/1.98  cnf(c_31971,plain,
% 11.66/1.98      ( $false ),
% 11.66/1.98      inference(equality_resolution_simp,[status(thm)],[c_31970]) ).
% 11.66/1.98  
% 11.66/1.98  
% 11.66/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.66/1.98  
% 11.66/1.98  ------                               Statistics
% 11.66/1.98  
% 11.66/1.98  ------ Selected
% 11.66/1.98  
% 11.66/1.98  total_time:                             1.105
% 11.66/1.98  
%------------------------------------------------------------------------------
