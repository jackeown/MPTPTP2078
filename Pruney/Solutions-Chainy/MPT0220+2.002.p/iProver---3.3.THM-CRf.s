%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:28 EST 2020

% Result     : Theorem 51.34s
% Output     : CNFRefutation 51.34s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 342 expanded)
%              Number of clauses        :   48 ( 100 expanded)
%              Number of leaves         :   26 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  184 ( 533 expanded)
%              Number of equality atoms :  107 ( 293 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f73,f72])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
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

fof(f23,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f23])).

fof(f32,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39])).

fof(f66,plain,(
    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f76,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f66,f67,f73,f72,f72])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f52,f50,f50,f67])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f33])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_463,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_466,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1421,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_463,c_466])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_675,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_16])).

cnf(c_181977,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1421,c_675])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_270,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_14,c_1])).

cnf(c_829,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_270])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_484,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_1042,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_11,c_484])).

cnf(c_1060,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_14,c_1042])).

cnf(c_3509,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_829,c_1060])).

cnf(c_734,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_467,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1222,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_467,c_466])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_465,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_472,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_470,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3009,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_470])).

cnf(c_3111,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_3009])).

cnf(c_3119,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_465,c_3111])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_464,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3199,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3119,c_464])).

cnf(c_3204,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_3199])).

cnf(c_3300,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_465,c_3204])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_471,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1336,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_465,c_471])).

cnf(c_3301,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1336,c_3204])).

cnf(c_3510,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3509,c_11,c_734,c_1222,c_3300,c_3301])).

cnf(c_3511,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3510,c_734])).

cnf(c_485,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_4036,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3511,c_485])).

cnf(c_4039,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4036,c_11])).

cnf(c_181978,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_181977,c_4039])).

cnf(c_181979,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_181978])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 51.34/7.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.34/7.01  
% 51.34/7.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.34/7.01  
% 51.34/7.01  ------  iProver source info
% 51.34/7.01  
% 51.34/7.01  git: date: 2020-06-30 10:37:57 +0100
% 51.34/7.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.34/7.01  git: non_committed_changes: false
% 51.34/7.01  git: last_make_outside_of_git: false
% 51.34/7.01  
% 51.34/7.01  ------ 
% 51.34/7.01  
% 51.34/7.01  ------ Input Options
% 51.34/7.01  
% 51.34/7.01  --out_options                           all
% 51.34/7.01  --tptp_safe_out                         true
% 51.34/7.01  --problem_path                          ""
% 51.34/7.01  --include_path                          ""
% 51.34/7.01  --clausifier                            res/vclausify_rel
% 51.34/7.01  --clausifier_options                    ""
% 51.34/7.01  --stdin                                 false
% 51.34/7.01  --stats_out                             all
% 51.34/7.01  
% 51.34/7.01  ------ General Options
% 51.34/7.01  
% 51.34/7.01  --fof                                   false
% 51.34/7.01  --time_out_real                         305.
% 51.34/7.01  --time_out_virtual                      -1.
% 51.34/7.01  --symbol_type_check                     false
% 51.34/7.01  --clausify_out                          false
% 51.34/7.01  --sig_cnt_out                           false
% 51.34/7.01  --trig_cnt_out                          false
% 51.34/7.01  --trig_cnt_out_tolerance                1.
% 51.34/7.01  --trig_cnt_out_sk_spl                   false
% 51.34/7.01  --abstr_cl_out                          false
% 51.34/7.01  
% 51.34/7.01  ------ Global Options
% 51.34/7.01  
% 51.34/7.01  --schedule                              default
% 51.34/7.01  --add_important_lit                     false
% 51.34/7.01  --prop_solver_per_cl                    1000
% 51.34/7.01  --min_unsat_core                        false
% 51.34/7.01  --soft_assumptions                      false
% 51.34/7.01  --soft_lemma_size                       3
% 51.34/7.01  --prop_impl_unit_size                   0
% 51.34/7.01  --prop_impl_unit                        []
% 51.34/7.01  --share_sel_clauses                     true
% 51.34/7.01  --reset_solvers                         false
% 51.34/7.01  --bc_imp_inh                            [conj_cone]
% 51.34/7.01  --conj_cone_tolerance                   3.
% 51.34/7.01  --extra_neg_conj                        none
% 51.34/7.01  --large_theory_mode                     true
% 51.34/7.01  --prolific_symb_bound                   200
% 51.34/7.01  --lt_threshold                          2000
% 51.34/7.01  --clause_weak_htbl                      true
% 51.34/7.01  --gc_record_bc_elim                     false
% 51.34/7.01  
% 51.34/7.01  ------ Preprocessing Options
% 51.34/7.01  
% 51.34/7.01  --preprocessing_flag                    true
% 51.34/7.01  --time_out_prep_mult                    0.1
% 51.34/7.01  --splitting_mode                        input
% 51.34/7.01  --splitting_grd                         true
% 51.34/7.01  --splitting_cvd                         false
% 51.34/7.01  --splitting_cvd_svl                     false
% 51.34/7.01  --splitting_nvd                         32
% 51.34/7.01  --sub_typing                            true
% 51.34/7.01  --prep_gs_sim                           true
% 51.34/7.01  --prep_unflatten                        true
% 51.34/7.01  --prep_res_sim                          true
% 51.34/7.01  --prep_upred                            true
% 51.34/7.01  --prep_sem_filter                       exhaustive
% 51.34/7.01  --prep_sem_filter_out                   false
% 51.34/7.01  --pred_elim                             true
% 51.34/7.01  --res_sim_input                         true
% 51.34/7.01  --eq_ax_congr_red                       true
% 51.34/7.01  --pure_diseq_elim                       true
% 51.34/7.01  --brand_transform                       false
% 51.34/7.01  --non_eq_to_eq                          false
% 51.34/7.01  --prep_def_merge                        true
% 51.34/7.01  --prep_def_merge_prop_impl              false
% 51.34/7.01  --prep_def_merge_mbd                    true
% 51.34/7.01  --prep_def_merge_tr_red                 false
% 51.34/7.01  --prep_def_merge_tr_cl                  false
% 51.34/7.01  --smt_preprocessing                     true
% 51.34/7.01  --smt_ac_axioms                         fast
% 51.34/7.01  --preprocessed_out                      false
% 51.34/7.01  --preprocessed_stats                    false
% 51.34/7.01  
% 51.34/7.01  ------ Abstraction refinement Options
% 51.34/7.01  
% 51.34/7.01  --abstr_ref                             []
% 51.34/7.01  --abstr_ref_prep                        false
% 51.34/7.01  --abstr_ref_until_sat                   false
% 51.34/7.01  --abstr_ref_sig_restrict                funpre
% 51.34/7.01  --abstr_ref_af_restrict_to_split_sk     false
% 51.34/7.01  --abstr_ref_under                       []
% 51.34/7.01  
% 51.34/7.01  ------ SAT Options
% 51.34/7.01  
% 51.34/7.01  --sat_mode                              false
% 51.34/7.01  --sat_fm_restart_options                ""
% 51.34/7.01  --sat_gr_def                            false
% 51.34/7.01  --sat_epr_types                         true
% 51.34/7.01  --sat_non_cyclic_types                  false
% 51.34/7.01  --sat_finite_models                     false
% 51.34/7.01  --sat_fm_lemmas                         false
% 51.34/7.01  --sat_fm_prep                           false
% 51.34/7.01  --sat_fm_uc_incr                        true
% 51.34/7.01  --sat_out_model                         small
% 51.34/7.01  --sat_out_clauses                       false
% 51.34/7.01  
% 51.34/7.01  ------ QBF Options
% 51.34/7.01  
% 51.34/7.01  --qbf_mode                              false
% 51.34/7.01  --qbf_elim_univ                         false
% 51.34/7.01  --qbf_dom_inst                          none
% 51.34/7.01  --qbf_dom_pre_inst                      false
% 51.34/7.01  --qbf_sk_in                             false
% 51.34/7.01  --qbf_pred_elim                         true
% 51.34/7.01  --qbf_split                             512
% 51.34/7.01  
% 51.34/7.01  ------ BMC1 Options
% 51.34/7.01  
% 51.34/7.01  --bmc1_incremental                      false
% 51.34/7.01  --bmc1_axioms                           reachable_all
% 51.34/7.01  --bmc1_min_bound                        0
% 51.34/7.01  --bmc1_max_bound                        -1
% 51.34/7.01  --bmc1_max_bound_default                -1
% 51.34/7.01  --bmc1_symbol_reachability              true
% 51.34/7.01  --bmc1_property_lemmas                  false
% 51.34/7.01  --bmc1_k_induction                      false
% 51.34/7.01  --bmc1_non_equiv_states                 false
% 51.34/7.01  --bmc1_deadlock                         false
% 51.34/7.01  --bmc1_ucm                              false
% 51.34/7.01  --bmc1_add_unsat_core                   none
% 51.34/7.01  --bmc1_unsat_core_children              false
% 51.34/7.01  --bmc1_unsat_core_extrapolate_axioms    false
% 51.34/7.01  --bmc1_out_stat                         full
% 51.34/7.01  --bmc1_ground_init                      false
% 51.34/7.01  --bmc1_pre_inst_next_state              false
% 51.34/7.01  --bmc1_pre_inst_state                   false
% 51.34/7.01  --bmc1_pre_inst_reach_state             false
% 51.34/7.01  --bmc1_out_unsat_core                   false
% 51.34/7.01  --bmc1_aig_witness_out                  false
% 51.34/7.01  --bmc1_verbose                          false
% 51.34/7.01  --bmc1_dump_clauses_tptp                false
% 51.34/7.01  --bmc1_dump_unsat_core_tptp             false
% 51.34/7.01  --bmc1_dump_file                        -
% 51.34/7.01  --bmc1_ucm_expand_uc_limit              128
% 51.34/7.01  --bmc1_ucm_n_expand_iterations          6
% 51.34/7.01  --bmc1_ucm_extend_mode                  1
% 51.34/7.01  --bmc1_ucm_init_mode                    2
% 51.34/7.01  --bmc1_ucm_cone_mode                    none
% 51.34/7.01  --bmc1_ucm_reduced_relation_type        0
% 51.34/7.01  --bmc1_ucm_relax_model                  4
% 51.34/7.01  --bmc1_ucm_full_tr_after_sat            true
% 51.34/7.01  --bmc1_ucm_expand_neg_assumptions       false
% 51.34/7.01  --bmc1_ucm_layered_model                none
% 51.34/7.01  --bmc1_ucm_max_lemma_size               10
% 51.34/7.01  
% 51.34/7.01  ------ AIG Options
% 51.34/7.01  
% 51.34/7.01  --aig_mode                              false
% 51.34/7.01  
% 51.34/7.01  ------ Instantiation Options
% 51.34/7.01  
% 51.34/7.01  --instantiation_flag                    true
% 51.34/7.01  --inst_sos_flag                         true
% 51.34/7.01  --inst_sos_phase                        true
% 51.34/7.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.34/7.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.34/7.01  --inst_lit_sel_side                     num_symb
% 51.34/7.01  --inst_solver_per_active                1400
% 51.34/7.01  --inst_solver_calls_frac                1.
% 51.34/7.01  --inst_passive_queue_type               priority_queues
% 51.34/7.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.34/7.01  --inst_passive_queues_freq              [25;2]
% 51.34/7.01  --inst_dismatching                      true
% 51.34/7.01  --inst_eager_unprocessed_to_passive     true
% 51.34/7.01  --inst_prop_sim_given                   true
% 51.34/7.01  --inst_prop_sim_new                     false
% 51.34/7.01  --inst_subs_new                         false
% 51.34/7.01  --inst_eq_res_simp                      false
% 51.34/7.01  --inst_subs_given                       false
% 51.34/7.01  --inst_orphan_elimination               true
% 51.34/7.01  --inst_learning_loop_flag               true
% 51.34/7.01  --inst_learning_start                   3000
% 51.34/7.01  --inst_learning_factor                  2
% 51.34/7.01  --inst_start_prop_sim_after_learn       3
% 51.34/7.01  --inst_sel_renew                        solver
% 51.34/7.01  --inst_lit_activity_flag                true
% 51.34/7.01  --inst_restr_to_given                   false
% 51.34/7.01  --inst_activity_threshold               500
% 51.34/7.01  --inst_out_proof                        true
% 51.34/7.01  
% 51.34/7.01  ------ Resolution Options
% 51.34/7.01  
% 51.34/7.01  --resolution_flag                       true
% 51.34/7.01  --res_lit_sel                           adaptive
% 51.34/7.01  --res_lit_sel_side                      none
% 51.34/7.01  --res_ordering                          kbo
% 51.34/7.01  --res_to_prop_solver                    active
% 51.34/7.01  --res_prop_simpl_new                    false
% 51.34/7.01  --res_prop_simpl_given                  true
% 51.34/7.01  --res_passive_queue_type                priority_queues
% 51.34/7.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.34/7.01  --res_passive_queues_freq               [15;5]
% 51.34/7.01  --res_forward_subs                      full
% 51.34/7.01  --res_backward_subs                     full
% 51.34/7.01  --res_forward_subs_resolution           true
% 51.34/7.01  --res_backward_subs_resolution          true
% 51.34/7.01  --res_orphan_elimination                true
% 51.34/7.01  --res_time_limit                        2.
% 51.34/7.01  --res_out_proof                         true
% 51.34/7.01  
% 51.34/7.01  ------ Superposition Options
% 51.34/7.01  
% 51.34/7.01  --superposition_flag                    true
% 51.34/7.01  --sup_passive_queue_type                priority_queues
% 51.34/7.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.34/7.01  --sup_passive_queues_freq               [8;1;4]
% 51.34/7.01  --demod_completeness_check              fast
% 51.34/7.01  --demod_use_ground                      true
% 51.34/7.01  --sup_to_prop_solver                    passive
% 51.34/7.01  --sup_prop_simpl_new                    true
% 51.34/7.01  --sup_prop_simpl_given                  true
% 51.34/7.01  --sup_fun_splitting                     true
% 51.34/7.01  --sup_smt_interval                      50000
% 51.34/7.01  
% 51.34/7.01  ------ Superposition Simplification Setup
% 51.34/7.01  
% 51.34/7.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.34/7.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.34/7.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.34/7.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.34/7.01  --sup_full_triv                         [TrivRules;PropSubs]
% 51.34/7.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.34/7.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.34/7.01  --sup_immed_triv                        [TrivRules]
% 51.34/7.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.01  --sup_immed_bw_main                     []
% 51.34/7.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.34/7.01  --sup_input_triv                        [Unflattening;TrivRules]
% 51.34/7.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.01  --sup_input_bw                          []
% 51.34/7.01  
% 51.34/7.01  ------ Combination Options
% 51.34/7.01  
% 51.34/7.01  --comb_res_mult                         3
% 51.34/7.01  --comb_sup_mult                         2
% 51.34/7.01  --comb_inst_mult                        10
% 51.34/7.01  
% 51.34/7.01  ------ Debug Options
% 51.34/7.01  
% 51.34/7.01  --dbg_backtrace                         false
% 51.34/7.01  --dbg_dump_prop_clauses                 false
% 51.34/7.01  --dbg_dump_prop_clauses_file            -
% 51.34/7.01  --dbg_out_stat                          false
% 51.34/7.01  ------ Parsing...
% 51.34/7.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.34/7.01  
% 51.34/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.34/7.01  
% 51.34/7.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.34/7.01  
% 51.34/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.34/7.01  ------ Proving...
% 51.34/7.01  ------ Problem Properties 
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  clauses                                 16
% 51.34/7.01  conjectures                             1
% 51.34/7.01  EPR                                     5
% 51.34/7.01  Horn                                    14
% 51.34/7.01  unary                                   9
% 51.34/7.01  binary                                  5
% 51.34/7.01  lits                                    25
% 51.34/7.01  lits eq                                 9
% 51.34/7.01  fd_pure                                 0
% 51.34/7.01  fd_pseudo                               0
% 51.34/7.01  fd_cond                                 0
% 51.34/7.01  fd_pseudo_cond                          2
% 51.34/7.01  AC symbols                              1
% 51.34/7.01  
% 51.34/7.01  ------ Schedule dynamic 5 is on 
% 51.34/7.01  
% 51.34/7.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  ------ 
% 51.34/7.01  Current options:
% 51.34/7.01  ------ 
% 51.34/7.01  
% 51.34/7.01  ------ Input Options
% 51.34/7.01  
% 51.34/7.01  --out_options                           all
% 51.34/7.01  --tptp_safe_out                         true
% 51.34/7.01  --problem_path                          ""
% 51.34/7.01  --include_path                          ""
% 51.34/7.01  --clausifier                            res/vclausify_rel
% 51.34/7.01  --clausifier_options                    ""
% 51.34/7.01  --stdin                                 false
% 51.34/7.01  --stats_out                             all
% 51.34/7.01  
% 51.34/7.01  ------ General Options
% 51.34/7.01  
% 51.34/7.01  --fof                                   false
% 51.34/7.01  --time_out_real                         305.
% 51.34/7.01  --time_out_virtual                      -1.
% 51.34/7.01  --symbol_type_check                     false
% 51.34/7.01  --clausify_out                          false
% 51.34/7.01  --sig_cnt_out                           false
% 51.34/7.01  --trig_cnt_out                          false
% 51.34/7.01  --trig_cnt_out_tolerance                1.
% 51.34/7.01  --trig_cnt_out_sk_spl                   false
% 51.34/7.01  --abstr_cl_out                          false
% 51.34/7.01  
% 51.34/7.01  ------ Global Options
% 51.34/7.01  
% 51.34/7.01  --schedule                              default
% 51.34/7.01  --add_important_lit                     false
% 51.34/7.01  --prop_solver_per_cl                    1000
% 51.34/7.01  --min_unsat_core                        false
% 51.34/7.01  --soft_assumptions                      false
% 51.34/7.01  --soft_lemma_size                       3
% 51.34/7.01  --prop_impl_unit_size                   0
% 51.34/7.01  --prop_impl_unit                        []
% 51.34/7.01  --share_sel_clauses                     true
% 51.34/7.01  --reset_solvers                         false
% 51.34/7.01  --bc_imp_inh                            [conj_cone]
% 51.34/7.01  --conj_cone_tolerance                   3.
% 51.34/7.01  --extra_neg_conj                        none
% 51.34/7.01  --large_theory_mode                     true
% 51.34/7.01  --prolific_symb_bound                   200
% 51.34/7.01  --lt_threshold                          2000
% 51.34/7.01  --clause_weak_htbl                      true
% 51.34/7.01  --gc_record_bc_elim                     false
% 51.34/7.01  
% 51.34/7.01  ------ Preprocessing Options
% 51.34/7.01  
% 51.34/7.01  --preprocessing_flag                    true
% 51.34/7.01  --time_out_prep_mult                    0.1
% 51.34/7.01  --splitting_mode                        input
% 51.34/7.01  --splitting_grd                         true
% 51.34/7.01  --splitting_cvd                         false
% 51.34/7.01  --splitting_cvd_svl                     false
% 51.34/7.01  --splitting_nvd                         32
% 51.34/7.01  --sub_typing                            true
% 51.34/7.01  --prep_gs_sim                           true
% 51.34/7.01  --prep_unflatten                        true
% 51.34/7.01  --prep_res_sim                          true
% 51.34/7.01  --prep_upred                            true
% 51.34/7.01  --prep_sem_filter                       exhaustive
% 51.34/7.01  --prep_sem_filter_out                   false
% 51.34/7.01  --pred_elim                             true
% 51.34/7.01  --res_sim_input                         true
% 51.34/7.01  --eq_ax_congr_red                       true
% 51.34/7.01  --pure_diseq_elim                       true
% 51.34/7.01  --brand_transform                       false
% 51.34/7.01  --non_eq_to_eq                          false
% 51.34/7.01  --prep_def_merge                        true
% 51.34/7.01  --prep_def_merge_prop_impl              false
% 51.34/7.01  --prep_def_merge_mbd                    true
% 51.34/7.01  --prep_def_merge_tr_red                 false
% 51.34/7.01  --prep_def_merge_tr_cl                  false
% 51.34/7.01  --smt_preprocessing                     true
% 51.34/7.01  --smt_ac_axioms                         fast
% 51.34/7.01  --preprocessed_out                      false
% 51.34/7.01  --preprocessed_stats                    false
% 51.34/7.01  
% 51.34/7.01  ------ Abstraction refinement Options
% 51.34/7.01  
% 51.34/7.01  --abstr_ref                             []
% 51.34/7.01  --abstr_ref_prep                        false
% 51.34/7.01  --abstr_ref_until_sat                   false
% 51.34/7.01  --abstr_ref_sig_restrict                funpre
% 51.34/7.01  --abstr_ref_af_restrict_to_split_sk     false
% 51.34/7.01  --abstr_ref_under                       []
% 51.34/7.01  
% 51.34/7.01  ------ SAT Options
% 51.34/7.01  
% 51.34/7.01  --sat_mode                              false
% 51.34/7.01  --sat_fm_restart_options                ""
% 51.34/7.01  --sat_gr_def                            false
% 51.34/7.01  --sat_epr_types                         true
% 51.34/7.01  --sat_non_cyclic_types                  false
% 51.34/7.01  --sat_finite_models                     false
% 51.34/7.01  --sat_fm_lemmas                         false
% 51.34/7.01  --sat_fm_prep                           false
% 51.34/7.01  --sat_fm_uc_incr                        true
% 51.34/7.01  --sat_out_model                         small
% 51.34/7.01  --sat_out_clauses                       false
% 51.34/7.01  
% 51.34/7.01  ------ QBF Options
% 51.34/7.01  
% 51.34/7.01  --qbf_mode                              false
% 51.34/7.01  --qbf_elim_univ                         false
% 51.34/7.01  --qbf_dom_inst                          none
% 51.34/7.01  --qbf_dom_pre_inst                      false
% 51.34/7.01  --qbf_sk_in                             false
% 51.34/7.01  --qbf_pred_elim                         true
% 51.34/7.01  --qbf_split                             512
% 51.34/7.01  
% 51.34/7.01  ------ BMC1 Options
% 51.34/7.01  
% 51.34/7.01  --bmc1_incremental                      false
% 51.34/7.01  --bmc1_axioms                           reachable_all
% 51.34/7.01  --bmc1_min_bound                        0
% 51.34/7.01  --bmc1_max_bound                        -1
% 51.34/7.01  --bmc1_max_bound_default                -1
% 51.34/7.01  --bmc1_symbol_reachability              true
% 51.34/7.01  --bmc1_property_lemmas                  false
% 51.34/7.01  --bmc1_k_induction                      false
% 51.34/7.01  --bmc1_non_equiv_states                 false
% 51.34/7.01  --bmc1_deadlock                         false
% 51.34/7.01  --bmc1_ucm                              false
% 51.34/7.01  --bmc1_add_unsat_core                   none
% 51.34/7.01  --bmc1_unsat_core_children              false
% 51.34/7.01  --bmc1_unsat_core_extrapolate_axioms    false
% 51.34/7.01  --bmc1_out_stat                         full
% 51.34/7.01  --bmc1_ground_init                      false
% 51.34/7.01  --bmc1_pre_inst_next_state              false
% 51.34/7.01  --bmc1_pre_inst_state                   false
% 51.34/7.01  --bmc1_pre_inst_reach_state             false
% 51.34/7.01  --bmc1_out_unsat_core                   false
% 51.34/7.01  --bmc1_aig_witness_out                  false
% 51.34/7.01  --bmc1_verbose                          false
% 51.34/7.01  --bmc1_dump_clauses_tptp                false
% 51.34/7.01  --bmc1_dump_unsat_core_tptp             false
% 51.34/7.01  --bmc1_dump_file                        -
% 51.34/7.01  --bmc1_ucm_expand_uc_limit              128
% 51.34/7.01  --bmc1_ucm_n_expand_iterations          6
% 51.34/7.01  --bmc1_ucm_extend_mode                  1
% 51.34/7.01  --bmc1_ucm_init_mode                    2
% 51.34/7.01  --bmc1_ucm_cone_mode                    none
% 51.34/7.01  --bmc1_ucm_reduced_relation_type        0
% 51.34/7.01  --bmc1_ucm_relax_model                  4
% 51.34/7.01  --bmc1_ucm_full_tr_after_sat            true
% 51.34/7.01  --bmc1_ucm_expand_neg_assumptions       false
% 51.34/7.01  --bmc1_ucm_layered_model                none
% 51.34/7.01  --bmc1_ucm_max_lemma_size               10
% 51.34/7.01  
% 51.34/7.01  ------ AIG Options
% 51.34/7.01  
% 51.34/7.01  --aig_mode                              false
% 51.34/7.01  
% 51.34/7.01  ------ Instantiation Options
% 51.34/7.01  
% 51.34/7.01  --instantiation_flag                    true
% 51.34/7.01  --inst_sos_flag                         true
% 51.34/7.01  --inst_sos_phase                        true
% 51.34/7.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.34/7.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.34/7.01  --inst_lit_sel_side                     none
% 51.34/7.01  --inst_solver_per_active                1400
% 51.34/7.01  --inst_solver_calls_frac                1.
% 51.34/7.01  --inst_passive_queue_type               priority_queues
% 51.34/7.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.34/7.01  --inst_passive_queues_freq              [25;2]
% 51.34/7.01  --inst_dismatching                      true
% 51.34/7.01  --inst_eager_unprocessed_to_passive     true
% 51.34/7.01  --inst_prop_sim_given                   true
% 51.34/7.01  --inst_prop_sim_new                     false
% 51.34/7.01  --inst_subs_new                         false
% 51.34/7.01  --inst_eq_res_simp                      false
% 51.34/7.01  --inst_subs_given                       false
% 51.34/7.01  --inst_orphan_elimination               true
% 51.34/7.01  --inst_learning_loop_flag               true
% 51.34/7.01  --inst_learning_start                   3000
% 51.34/7.01  --inst_learning_factor                  2
% 51.34/7.01  --inst_start_prop_sim_after_learn       3
% 51.34/7.01  --inst_sel_renew                        solver
% 51.34/7.01  --inst_lit_activity_flag                true
% 51.34/7.01  --inst_restr_to_given                   false
% 51.34/7.01  --inst_activity_threshold               500
% 51.34/7.01  --inst_out_proof                        true
% 51.34/7.01  
% 51.34/7.01  ------ Resolution Options
% 51.34/7.01  
% 51.34/7.01  --resolution_flag                       false
% 51.34/7.01  --res_lit_sel                           adaptive
% 51.34/7.01  --res_lit_sel_side                      none
% 51.34/7.01  --res_ordering                          kbo
% 51.34/7.01  --res_to_prop_solver                    active
% 51.34/7.01  --res_prop_simpl_new                    false
% 51.34/7.01  --res_prop_simpl_given                  true
% 51.34/7.01  --res_passive_queue_type                priority_queues
% 51.34/7.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.34/7.01  --res_passive_queues_freq               [15;5]
% 51.34/7.01  --res_forward_subs                      full
% 51.34/7.01  --res_backward_subs                     full
% 51.34/7.01  --res_forward_subs_resolution           true
% 51.34/7.01  --res_backward_subs_resolution          true
% 51.34/7.01  --res_orphan_elimination                true
% 51.34/7.01  --res_time_limit                        2.
% 51.34/7.01  --res_out_proof                         true
% 51.34/7.01  
% 51.34/7.01  ------ Superposition Options
% 51.34/7.01  
% 51.34/7.01  --superposition_flag                    true
% 51.34/7.01  --sup_passive_queue_type                priority_queues
% 51.34/7.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.34/7.01  --sup_passive_queues_freq               [8;1;4]
% 51.34/7.01  --demod_completeness_check              fast
% 51.34/7.01  --demod_use_ground                      true
% 51.34/7.01  --sup_to_prop_solver                    passive
% 51.34/7.01  --sup_prop_simpl_new                    true
% 51.34/7.01  --sup_prop_simpl_given                  true
% 51.34/7.01  --sup_fun_splitting                     true
% 51.34/7.01  --sup_smt_interval                      50000
% 51.34/7.01  
% 51.34/7.01  ------ Superposition Simplification Setup
% 51.34/7.01  
% 51.34/7.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.34/7.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.34/7.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.34/7.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.34/7.01  --sup_full_triv                         [TrivRules;PropSubs]
% 51.34/7.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.34/7.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.34/7.01  --sup_immed_triv                        [TrivRules]
% 51.34/7.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.01  --sup_immed_bw_main                     []
% 51.34/7.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.34/7.01  --sup_input_triv                        [Unflattening;TrivRules]
% 51.34/7.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.01  --sup_input_bw                          []
% 51.34/7.01  
% 51.34/7.01  ------ Combination Options
% 51.34/7.01  
% 51.34/7.01  --comb_res_mult                         3
% 51.34/7.01  --comb_sup_mult                         2
% 51.34/7.01  --comb_inst_mult                        10
% 51.34/7.01  
% 51.34/7.01  ------ Debug Options
% 51.34/7.01  
% 51.34/7.01  --dbg_backtrace                         false
% 51.34/7.01  --dbg_dump_prop_clauses                 false
% 51.34/7.01  --dbg_dump_prop_clauses_file            -
% 51.34/7.01  --dbg_out_stat                          false
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  ------ Proving...
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  % SZS status Theorem for theBenchmark.p
% 51.34/7.01  
% 51.34/7.01   Resolution empty clause
% 51.34/7.01  
% 51.34/7.01  % SZS output start CNFRefutation for theBenchmark.p
% 51.34/7.01  
% 51.34/7.01  fof(f22,axiom,(
% 51.34/7.01    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f65,plain,(
% 51.34/7.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 51.34/7.01    inference(cnf_transformation,[],[f22])).
% 51.34/7.01  
% 51.34/7.01  fof(f15,axiom,(
% 51.34/7.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f58,plain,(
% 51.34/7.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f15])).
% 51.34/7.01  
% 51.34/7.01  fof(f73,plain,(
% 51.34/7.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 51.34/7.01    inference(definition_unfolding,[],[f58,f72])).
% 51.34/7.01  
% 51.34/7.01  fof(f16,axiom,(
% 51.34/7.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f59,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f16])).
% 51.34/7.01  
% 51.34/7.01  fof(f17,axiom,(
% 51.34/7.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f60,plain,(
% 51.34/7.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f17])).
% 51.34/7.01  
% 51.34/7.01  fof(f18,axiom,(
% 51.34/7.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f61,plain,(
% 51.34/7.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f18])).
% 51.34/7.01  
% 51.34/7.01  fof(f19,axiom,(
% 51.34/7.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f62,plain,(
% 51.34/7.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f19])).
% 51.34/7.01  
% 51.34/7.01  fof(f20,axiom,(
% 51.34/7.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f63,plain,(
% 51.34/7.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f20])).
% 51.34/7.01  
% 51.34/7.01  fof(f21,axiom,(
% 51.34/7.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f64,plain,(
% 51.34/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f21])).
% 51.34/7.01  
% 51.34/7.01  fof(f68,plain,(
% 51.34/7.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.34/7.01    inference(definition_unfolding,[],[f63,f64])).
% 51.34/7.01  
% 51.34/7.01  fof(f69,plain,(
% 51.34/7.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.34/7.01    inference(definition_unfolding,[],[f62,f68])).
% 51.34/7.01  
% 51.34/7.01  fof(f70,plain,(
% 51.34/7.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.34/7.01    inference(definition_unfolding,[],[f61,f69])).
% 51.34/7.01  
% 51.34/7.01  fof(f71,plain,(
% 51.34/7.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.34/7.01    inference(definition_unfolding,[],[f60,f70])).
% 51.34/7.01  
% 51.34/7.01  fof(f72,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.34/7.01    inference(definition_unfolding,[],[f59,f71])).
% 51.34/7.01  
% 51.34/7.01  fof(f75,plain,(
% 51.34/7.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.34/7.01    inference(definition_unfolding,[],[f65,f73,f72])).
% 51.34/7.01  
% 51.34/7.01  fof(f8,axiom,(
% 51.34/7.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f30,plain,(
% 51.34/7.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.34/7.01    inference(ennf_transformation,[],[f8])).
% 51.34/7.01  
% 51.34/7.01  fof(f51,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f30])).
% 51.34/7.01  
% 51.34/7.01  fof(f1,axiom,(
% 51.34/7.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f41,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f1])).
% 51.34/7.01  
% 51.34/7.01  fof(f23,conjecture,(
% 51.34/7.01    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f24,negated_conjecture,(
% 51.34/7.01    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 51.34/7.01    inference(negated_conjecture,[],[f23])).
% 51.34/7.01  
% 51.34/7.01  fof(f32,plain,(
% 51.34/7.01    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 51.34/7.01    inference(ennf_transformation,[],[f24])).
% 51.34/7.01  
% 51.34/7.01  fof(f39,plain,(
% 51.34/7.01    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3)),
% 51.34/7.01    introduced(choice_axiom,[])).
% 51.34/7.01  
% 51.34/7.01  fof(f40,plain,(
% 51.34/7.01    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3)),
% 51.34/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39])).
% 51.34/7.01  
% 51.34/7.01  fof(f66,plain,(
% 51.34/7.01    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) != k2_tarski(sK2,sK3)),
% 51.34/7.01    inference(cnf_transformation,[],[f40])).
% 51.34/7.01  
% 51.34/7.01  fof(f14,axiom,(
% 51.34/7.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f57,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f14])).
% 51.34/7.01  
% 51.34/7.01  fof(f7,axiom,(
% 51.34/7.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f50,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f7])).
% 51.34/7.01  
% 51.34/7.01  fof(f67,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 51.34/7.01    inference(definition_unfolding,[],[f57,f50])).
% 51.34/7.01  
% 51.34/7.01  fof(f76,plain,(
% 51.34/7.01    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 51.34/7.01    inference(definition_unfolding,[],[f66,f67,f73,f72,f72])).
% 51.34/7.01  
% 51.34/7.01  fof(f9,axiom,(
% 51.34/7.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f52,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f9])).
% 51.34/7.01  
% 51.34/7.01  fof(f74,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 51.34/7.01    inference(definition_unfolding,[],[f52,f50,f50,f67])).
% 51.34/7.01  
% 51.34/7.01  fof(f13,axiom,(
% 51.34/7.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f56,plain,(
% 51.34/7.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f13])).
% 51.34/7.01  
% 51.34/7.01  fof(f2,axiom,(
% 51.34/7.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f42,plain,(
% 51.34/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f2])).
% 51.34/7.01  
% 51.34/7.01  fof(f10,axiom,(
% 51.34/7.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f53,plain,(
% 51.34/7.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.34/7.01    inference(cnf_transformation,[],[f10])).
% 51.34/7.01  
% 51.34/7.01  fof(f6,axiom,(
% 51.34/7.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f37,plain,(
% 51.34/7.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.34/7.01    inference(nnf_transformation,[],[f6])).
% 51.34/7.01  
% 51.34/7.01  fof(f38,plain,(
% 51.34/7.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.34/7.01    inference(flattening,[],[f37])).
% 51.34/7.01  
% 51.34/7.01  fof(f47,plain,(
% 51.34/7.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.34/7.01    inference(cnf_transformation,[],[f38])).
% 51.34/7.01  
% 51.34/7.01  fof(f78,plain,(
% 51.34/7.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.34/7.01    inference(equality_resolution,[],[f47])).
% 51.34/7.01  
% 51.34/7.01  fof(f11,axiom,(
% 51.34/7.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f54,plain,(
% 51.34/7.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f11])).
% 51.34/7.01  
% 51.34/7.01  fof(f3,axiom,(
% 51.34/7.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f26,plain,(
% 51.34/7.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 51.34/7.01    inference(unused_predicate_definition_removal,[],[f3])).
% 51.34/7.01  
% 51.34/7.01  fof(f27,plain,(
% 51.34/7.01    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 51.34/7.01    inference(ennf_transformation,[],[f26])).
% 51.34/7.01  
% 51.34/7.01  fof(f33,plain,(
% 51.34/7.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 51.34/7.01    introduced(choice_axiom,[])).
% 51.34/7.01  
% 51.34/7.01  fof(f34,plain,(
% 51.34/7.01    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 51.34/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f33])).
% 51.34/7.01  
% 51.34/7.01  fof(f43,plain,(
% 51.34/7.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f34])).
% 51.34/7.01  
% 51.34/7.01  fof(f5,axiom,(
% 51.34/7.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f25,plain,(
% 51.34/7.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.34/7.01    inference(rectify,[],[f5])).
% 51.34/7.01  
% 51.34/7.01  fof(f29,plain,(
% 51.34/7.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.34/7.01    inference(ennf_transformation,[],[f25])).
% 51.34/7.01  
% 51.34/7.01  fof(f35,plain,(
% 51.34/7.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 51.34/7.01    introduced(choice_axiom,[])).
% 51.34/7.01  
% 51.34/7.01  fof(f36,plain,(
% 51.34/7.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.34/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f35])).
% 51.34/7.01  
% 51.34/7.01  fof(f46,plain,(
% 51.34/7.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 51.34/7.01    inference(cnf_transformation,[],[f36])).
% 51.34/7.01  
% 51.34/7.01  fof(f12,axiom,(
% 51.34/7.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f31,plain,(
% 51.34/7.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 51.34/7.01    inference(ennf_transformation,[],[f12])).
% 51.34/7.01  
% 51.34/7.01  fof(f55,plain,(
% 51.34/7.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f31])).
% 51.34/7.01  
% 51.34/7.01  fof(f4,axiom,(
% 51.34/7.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 51.34/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.01  
% 51.34/7.01  fof(f28,plain,(
% 51.34/7.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 51.34/7.01    inference(ennf_transformation,[],[f4])).
% 51.34/7.01  
% 51.34/7.01  fof(f44,plain,(
% 51.34/7.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 51.34/7.01    inference(cnf_transformation,[],[f28])).
% 51.34/7.01  
% 51.34/7.01  cnf(c_15,plain,
% 51.34/7.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 51.34/7.01      inference(cnf_transformation,[],[f75]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_463,plain,
% 51.34/7.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_9,plain,
% 51.34/7.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.34/7.01      inference(cnf_transformation,[],[f51]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_466,plain,
% 51.34/7.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_1421,plain,
% 51.34/7.01      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_463,c_466]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_0,plain,
% 51.34/7.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.34/7.01      inference(cnf_transformation,[],[f41]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_16,negated_conjecture,
% 51.34/7.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 51.34/7.01      inference(cnf_transformation,[],[f76]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_675,plain,
% 51.34/7.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 51.34/7.01      inference(demodulation,[status(thm)],[c_0,c_16]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_181977,plain,
% 51.34/7.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 51.34/7.01      inference(demodulation,[status(thm)],[c_1421,c_675]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_10,plain,
% 51.34/7.01      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.34/7.01      inference(cnf_transformation,[],[f74]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_14,plain,
% 51.34/7.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 51.34/7.01      inference(cnf_transformation,[],[f56]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_1,plain,
% 51.34/7.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 51.34/7.01      inference(cnf_transformation,[],[f42]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_270,plain,
% 51.34/7.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.34/7.01      inference(theory_normalisation,[status(thm)],[c_10,c_14,c_1]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_829,plain,
% 51.34/7.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_0,c_270]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_11,plain,
% 51.34/7.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.34/7.01      inference(cnf_transformation,[],[f53]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_484,plain,
% 51.34/7.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_14,c_1]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_1042,plain,
% 51.34/7.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_11,c_484]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_1060,plain,
% 51.34/7.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_14,c_1042]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3509,plain,
% 51.34/7.01      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_829,c_1060]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_734,plain,
% 51.34/7.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_8,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f78]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_467,plain,
% 51.34/7.01      ( r1_tarski(X0,X0) = iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_1222,plain,
% 51.34/7.01      ( k3_xboole_0(X0,X0) = X0 ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_467,c_466]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_12,plain,
% 51.34/7.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 51.34/7.01      inference(cnf_transformation,[],[f54]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_465,plain,
% 51.34/7.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_2,plain,
% 51.34/7.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 51.34/7.01      inference(cnf_transformation,[],[f43]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_472,plain,
% 51.34/7.01      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_4,plain,
% 51.34/7.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 51.34/7.01      inference(cnf_transformation,[],[f46]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_470,plain,
% 51.34/7.01      ( r1_xboole_0(X0,X1) != iProver_top
% 51.34/7.01      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3009,plain,
% 51.34/7.01      ( r1_xboole_0(X0,X1) != iProver_top
% 51.34/7.01      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_472,c_470]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3111,plain,
% 51.34/7.01      ( r1_xboole_0(X0,X0) != iProver_top | v1_xboole_0(X0) = iProver_top ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_1222,c_3009]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3119,plain,
% 51.34/7.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_465,c_3111]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_13,plain,
% 51.34/7.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 51.34/7.01      inference(cnf_transformation,[],[f55]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_464,plain,
% 51.34/7.01      ( X0 = X1
% 51.34/7.01      | v1_xboole_0(X0) != iProver_top
% 51.34/7.01      | v1_xboole_0(X1) != iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3199,plain,
% 51.34/7.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_3119,c_464]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3204,plain,
% 51.34/7.01      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_3009,c_3199]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3300,plain,
% 51.34/7.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_465,c_3204]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3,plain,
% 51.34/7.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 51.34/7.01      inference(cnf_transformation,[],[f44]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_471,plain,
% 51.34/7.01      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 51.34/7.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_1336,plain,
% 51.34/7.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_465,c_471]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3301,plain,
% 51.34/7.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_1336,c_3204]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3510,plain,
% 51.34/7.01      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 51.34/7.01      inference(light_normalisation,
% 51.34/7.01                [status(thm)],
% 51.34/7.01                [c_3509,c_11,c_734,c_1222,c_3300,c_3301]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_3511,plain,
% 51.34/7.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.34/7.01      inference(demodulation,[status(thm)],[c_3510,c_734]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_485,plain,
% 51.34/7.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_14,c_1]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_4036,plain,
% 51.34/7.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 51.34/7.01      inference(superposition,[status(thm)],[c_3511,c_485]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_4039,plain,
% 51.34/7.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 51.34/7.01      inference(demodulation,[status(thm)],[c_4036,c_11]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_181978,plain,
% 51.34/7.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 51.34/7.01      inference(demodulation,[status(thm)],[c_181977,c_4039]) ).
% 51.34/7.01  
% 51.34/7.01  cnf(c_181979,plain,
% 51.34/7.01      ( $false ),
% 51.34/7.01      inference(equality_resolution_simp,[status(thm)],[c_181978]) ).
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  % SZS output end CNFRefutation for theBenchmark.p
% 51.34/7.01  
% 51.34/7.01  ------                               Statistics
% 51.34/7.01  
% 51.34/7.01  ------ General
% 51.34/7.01  
% 51.34/7.01  abstr_ref_over_cycles:                  0
% 51.34/7.01  abstr_ref_under_cycles:                 0
% 51.34/7.01  gc_basic_clause_elim:                   0
% 51.34/7.01  forced_gc_time:                         0
% 51.34/7.01  parsing_time:                           0.021
% 51.34/7.01  unif_index_cands_time:                  0.
% 51.34/7.01  unif_index_add_time:                    0.
% 51.34/7.01  orderings_time:                         0.
% 51.34/7.01  out_proof_time:                         0.015
% 51.34/7.01  total_time:                             6.296
% 51.34/7.01  num_of_symbols:                         43
% 51.34/7.01  num_of_terms:                           380386
% 51.34/7.01  
% 51.34/7.01  ------ Preprocessing
% 51.34/7.01  
% 51.34/7.01  num_of_splits:                          0
% 51.34/7.01  num_of_split_atoms:                     0
% 51.34/7.01  num_of_reused_defs:                     0
% 51.34/7.01  num_eq_ax_congr_red:                    15
% 51.34/7.01  num_of_sem_filtered_clauses:            1
% 51.34/7.01  num_of_subtypes:                        0
% 51.34/7.01  monotx_restored_types:                  0
% 51.34/7.01  sat_num_of_epr_types:                   0
% 51.34/7.01  sat_num_of_non_cyclic_types:            0
% 51.34/7.01  sat_guarded_non_collapsed_types:        0
% 51.34/7.01  num_pure_diseq_elim:                    0
% 51.34/7.01  simp_replaced_by:                       0
% 51.34/7.01  res_preprocessed:                       81
% 51.34/7.01  prep_upred:                             0
% 51.34/7.01  prep_unflattend:                        6
% 51.34/7.01  smt_new_axioms:                         0
% 51.34/7.01  pred_elim_cands:                        4
% 51.34/7.01  pred_elim:                              0
% 51.34/7.01  pred_elim_cl:                           0
% 51.34/7.01  pred_elim_cycles:                       2
% 51.34/7.01  merged_defs:                            0
% 51.34/7.01  merged_defs_ncl:                        0
% 51.34/7.01  bin_hyper_res:                          0
% 51.34/7.01  prep_cycles:                            4
% 51.34/7.01  pred_elim_time:                         0.001
% 51.34/7.01  splitting_time:                         0.
% 51.34/7.01  sem_filter_time:                        0.
% 51.34/7.01  monotx_time:                            0.001
% 51.34/7.01  subtype_inf_time:                       0.
% 51.34/7.01  
% 51.34/7.01  ------ Problem properties
% 51.34/7.01  
% 51.34/7.01  clauses:                                16
% 51.34/7.01  conjectures:                            1
% 51.34/7.01  epr:                                    5
% 51.34/7.01  horn:                                   14
% 51.34/7.01  ground:                                 1
% 51.34/7.01  unary:                                  9
% 51.34/7.01  binary:                                 5
% 51.34/7.01  lits:                                   25
% 51.34/7.01  lits_eq:                                9
% 51.34/7.01  fd_pure:                                0
% 51.34/7.01  fd_pseudo:                              0
% 51.34/7.01  fd_cond:                                0
% 51.34/7.01  fd_pseudo_cond:                         2
% 51.34/7.01  ac_symbols:                             1
% 51.34/7.01  
% 51.34/7.01  ------ Propositional Solver
% 51.34/7.01  
% 51.34/7.01  prop_solver_calls:                      36
% 51.34/7.01  prop_fast_solver_calls:                 678
% 51.34/7.01  smt_solver_calls:                       0
% 51.34/7.01  smt_fast_solver_calls:                  0
% 51.34/7.01  prop_num_of_clauses:                    21975
% 51.34/7.01  prop_preprocess_simplified:             34333
% 51.34/7.01  prop_fo_subsumed:                       2
% 51.34/7.01  prop_solver_time:                       0.
% 51.34/7.01  smt_solver_time:                        0.
% 51.34/7.01  smt_fast_solver_time:                   0.
% 51.34/7.01  prop_fast_solver_time:                  0.
% 51.34/7.01  prop_unsat_core_time:                   0.
% 51.34/7.01  
% 51.34/7.01  ------ QBF
% 51.34/7.01  
% 51.34/7.01  qbf_q_res:                              0
% 51.34/7.01  qbf_num_tautologies:                    0
% 51.34/7.01  qbf_prep_cycles:                        0
% 51.34/7.01  
% 51.34/7.01  ------ BMC1
% 51.34/7.01  
% 51.34/7.01  bmc1_current_bound:                     -1
% 51.34/7.01  bmc1_last_solved_bound:                 -1
% 51.34/7.01  bmc1_unsat_core_size:                   -1
% 51.34/7.01  bmc1_unsat_core_parents_size:           -1
% 51.34/7.01  bmc1_merge_next_fun:                    0
% 51.34/7.01  bmc1_unsat_core_clauses_time:           0.
% 51.34/7.01  
% 51.34/7.01  ------ Instantiation
% 51.34/7.01  
% 51.34/7.01  inst_num_of_clauses:                    3954
% 51.34/7.01  inst_num_in_passive:                    2402
% 51.34/7.01  inst_num_in_active:                     880
% 51.34/7.01  inst_num_in_unprocessed:                672
% 51.34/7.01  inst_num_of_loops:                      1250
% 51.34/7.01  inst_num_of_learning_restarts:          0
% 51.34/7.01  inst_num_moves_active_passive:          364
% 51.34/7.01  inst_lit_activity:                      0
% 51.34/7.01  inst_lit_activity_moves:                1
% 51.34/7.01  inst_num_tautologies:                   0
% 51.34/7.01  inst_num_prop_implied:                  0
% 51.34/7.01  inst_num_existing_simplified:           0
% 51.34/7.01  inst_num_eq_res_simplified:             0
% 51.34/7.01  inst_num_child_elim:                    0
% 51.34/7.01  inst_num_of_dismatching_blockings:      3135
% 51.34/7.01  inst_num_of_non_proper_insts:           5561
% 51.34/7.01  inst_num_of_duplicates:                 0
% 51.34/7.01  inst_inst_num_from_inst_to_res:         0
% 51.34/7.01  inst_dismatching_checking_time:         0.
% 51.34/7.01  
% 51.34/7.01  ------ Resolution
% 51.34/7.01  
% 51.34/7.01  res_num_of_clauses:                     0
% 51.34/7.01  res_num_in_passive:                     0
% 51.34/7.01  res_num_in_active:                      0
% 51.34/7.01  res_num_of_loops:                       85
% 51.34/7.01  res_forward_subset_subsumed:            1191
% 51.34/7.01  res_backward_subset_subsumed:           0
% 51.34/7.01  res_forward_subsumed:                   0
% 51.34/7.01  res_backward_subsumed:                  0
% 51.34/7.01  res_forward_subsumption_resolution:     0
% 51.34/7.01  res_backward_subsumption_resolution:    0
% 51.34/7.01  res_clause_to_clause_subsumption:       777029
% 51.34/7.01  res_orphan_elimination:                 0
% 51.34/7.01  res_tautology_del:                      460
% 51.34/7.01  res_num_eq_res_simplified:              0
% 51.34/7.01  res_num_sel_changes:                    0
% 51.34/7.01  res_moves_from_active_to_pass:          0
% 51.34/7.01  
% 51.34/7.01  ------ Superposition
% 51.34/7.01  
% 51.34/7.01  sup_time_total:                         0.
% 51.34/7.01  sup_time_generating:                    0.
% 51.34/7.01  sup_time_sim_full:                      0.
% 51.34/7.01  sup_time_sim_immed:                     0.
% 51.34/7.01  
% 51.34/7.01  sup_num_of_clauses:                     11014
% 51.34/7.01  sup_num_in_active:                      226
% 51.34/7.01  sup_num_in_passive:                     10788
% 51.34/7.01  sup_num_of_loops:                       248
% 51.34/7.01  sup_fw_superposition:                   45847
% 51.34/7.01  sup_bw_superposition:                   41799
% 51.34/7.01  sup_immediate_simplified:               51810
% 51.34/7.01  sup_given_eliminated:                   6
% 51.34/7.01  comparisons_done:                       0
% 51.34/7.01  comparisons_avoided:                    0
% 51.34/7.01  
% 51.34/7.01  ------ Simplifications
% 51.34/7.01  
% 51.34/7.01  
% 51.34/7.01  sim_fw_subset_subsumed:                 4
% 51.34/7.01  sim_bw_subset_subsumed:                 0
% 51.34/7.01  sim_fw_subsumed:                        3002
% 51.34/7.01  sim_bw_subsumed:                        34
% 51.34/7.01  sim_fw_subsumption_res:                 0
% 51.34/7.01  sim_bw_subsumption_res:                 0
% 51.34/7.01  sim_tautology_del:                      2
% 51.34/7.01  sim_eq_tautology_del:                   11588
% 51.34/7.01  sim_eq_res_simp:                        0
% 51.34/7.01  sim_fw_demodulated:                     51894
% 51.34/7.01  sim_bw_demodulated:                     235
% 51.34/7.01  sim_light_normalised:                   12336
% 51.34/7.01  sim_joinable_taut:                      1747
% 51.34/7.01  sim_joinable_simp:                      0
% 51.34/7.01  sim_ac_normalised:                      0
% 51.34/7.01  sim_smt_subsumption:                    0
% 51.34/7.01  
%------------------------------------------------------------------------------
