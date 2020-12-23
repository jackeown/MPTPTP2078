%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:44 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 349 expanded)
%              Number of clauses        :   30 (  33 expanded)
%              Number of leaves         :   23 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 387 expanded)
%              Number of equality atoms :  112 ( 358 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f26])).

fof(f33,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f27])).

fof(f35,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35])).

fof(f63,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f67,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f83,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f63,f68,f67])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f50,f68,f57,f71])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f60,f70,f71,f71,f71])).

fof(f84,plain,(
    ! [X1] : k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f51,f68,f57,f67])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f39,f69])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f38,f68])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f49,f66,f66])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_148,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_463,plain,
    ( v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_148])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_34,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5963,plain,
    ( v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_34])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_492,plain,
    ( v1_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) != iProver_top
    | v1_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_148])).

cnf(c_10289,plain,
    ( v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5963,c_492])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5718,plain,
    ( ~ v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | k1_xboole_0 = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5719,plain,
    ( k1_xboole_0 = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)
    | v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5718])).

cnf(c_5721,plain,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5719])).

cnf(c_67,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_281,plain,
    ( X0 != X1
    | X0 = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_457,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1097,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | k1_xboole_0 != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_1098,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | k1_xboole_0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_167,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_2,c_10])).

cnf(c_189,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14,c_10,c_12,c_167])).

cnf(c_201,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_11,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_20,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10289,c_5721,c_1098,c_201,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.57/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.99  
% 3.57/0.99  ------  iProver source info
% 3.57/0.99  
% 3.57/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.99  git: non_committed_changes: false
% 3.57/0.99  git: last_make_outside_of_git: false
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    --mode clausify
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             sel
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         604.99
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              none
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           false
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             false
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         false
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     num_symb
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       true
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     false
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   []
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_full_bw                           [BwDemod]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  ------ Parsing...
% 3.57/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.99  ------ Proving...
% 3.57/0.99  ------ Problem Properties 
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  clauses                                 17
% 3.57/0.99  conjectures                             1
% 3.57/0.99  EPR                                     2
% 3.57/0.99  Horn                                    16
% 3.57/0.99  unary                                   13
% 3.57/0.99  binary                                  4
% 3.57/0.99  lits                                    21
% 3.57/0.99  lits eq                                 15
% 3.57/0.99  fd_pure                                 0
% 3.57/0.99  fd_pseudo                               0
% 3.57/0.99  fd_cond                                 1
% 3.57/0.99  fd_pseudo_cond                          1
% 3.57/0.99  AC symbols                              0
% 3.57/0.99  
% 3.57/0.99  ------ Input Options Time Limit: Unbounded
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  Current options:
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    --mode clausify
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             sel
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         604.99
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              none
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           false
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             false
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         false
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     num_symb
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       true
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     false
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   []
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_full_bw                           [BwDemod]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ Proving...
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS status Theorem for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  fof(f26,conjecture,(
% 3.57/0.99    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f27,negated_conjecture,(
% 3.57/0.99    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 3.57/0.99    inference(negated_conjecture,[],[f26])).
% 3.57/0.99  
% 3.57/0.99  fof(f33,plain,(
% 3.57/0.99    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 3.57/0.99    inference(ennf_transformation,[],[f27])).
% 3.57/0.99  
% 3.57/0.99  fof(f35,plain,(
% 3.57/0.99    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f36,plain,(
% 3.57/0.99    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35])).
% 3.57/0.99  
% 3.57/0.99  fof(f63,plain,(
% 3.57/0.99    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.57/0.99    inference(cnf_transformation,[],[f36])).
% 3.57/0.99  
% 3.57/0.99  fof(f23,axiom,(
% 3.57/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f59,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f23])).
% 3.57/0.99  
% 3.57/0.99  fof(f68,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f59,f67])).
% 3.57/0.99  
% 3.57/0.99  fof(f17,axiom,(
% 3.57/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f53,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f17])).
% 3.57/0.99  
% 3.57/0.99  fof(f18,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f54,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f18])).
% 3.57/0.99  
% 3.57/0.99  fof(f19,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f55,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f19])).
% 3.57/0.99  
% 3.57/0.99  fof(f20,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f56,plain,(
% 3.57/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f20])).
% 3.57/0.99  
% 3.57/0.99  fof(f21,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f57,plain,(
% 3.57/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f21])).
% 3.57/0.99  
% 3.57/0.99  fof(f64,plain,(
% 3.57/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f56,f57])).
% 3.57/0.99  
% 3.57/0.99  fof(f65,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f55,f64])).
% 3.57/0.99  
% 3.57/0.99  fof(f66,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f54,f65])).
% 3.57/0.99  
% 3.57/0.99  fof(f67,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f53,f66])).
% 3.57/0.99  
% 3.57/0.99  fof(f83,plain,(
% 3.57/0.99    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 3.57/0.99    inference(definition_unfolding,[],[f63,f68,f67])).
% 3.57/0.99  
% 3.57/0.99  fof(f5,axiom,(
% 3.57/0.99    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X0,X1)))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f31,plain,(
% 3.57/0.99    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f5])).
% 3.57/0.99  
% 3.57/0.99  fof(f41,plain,(
% 3.57/0.99    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f31])).
% 3.57/0.99  
% 3.57/0.99  fof(f76,plain,(
% 3.57/0.99    ( ! [X0,X1] : (~v1_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | v1_xboole_0(X0)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f41,f68])).
% 3.57/0.99  
% 3.57/0.99  fof(f1,axiom,(
% 3.57/0.99    v1_xboole_0(k1_xboole_0)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f37,plain,(
% 3.57/0.99    v1_xboole_0(k1_xboole_0)),
% 3.57/0.99    inference(cnf_transformation,[],[f1])).
% 3.57/0.99  
% 3.57/0.99  fof(f14,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f50,plain,(
% 3.57/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f14])).
% 3.57/0.99  
% 3.57/0.99  fof(f16,axiom,(
% 3.57/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f52,plain,(
% 3.57/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f16])).
% 3.57/0.99  
% 3.57/0.99  fof(f71,plain,(
% 3.57/0.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f52,f67])).
% 3.57/0.99  
% 3.57/0.99  fof(f73,plain,(
% 3.57/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f50,f68,f57,f71])).
% 3.57/0.99  
% 3.57/0.99  fof(f4,axiom,(
% 3.57/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f30,plain,(
% 3.57/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f4])).
% 3.57/0.99  
% 3.57/0.99  fof(f40,plain,(
% 3.57/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f30])).
% 3.57/0.99  
% 3.57/0.99  fof(f24,axiom,(
% 3.57/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f34,plain,(
% 3.57/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.57/0.99    inference(nnf_transformation,[],[f24])).
% 3.57/0.99  
% 3.57/0.99  fof(f60,plain,(
% 3.57/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f34])).
% 3.57/0.99  
% 3.57/0.99  fof(f7,axiom,(
% 3.57/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f43,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f7])).
% 3.57/0.99  
% 3.57/0.99  fof(f12,axiom,(
% 3.57/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f48,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f12])).
% 3.57/0.99  
% 3.57/0.99  fof(f69,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f48,f68])).
% 3.57/0.99  
% 3.57/0.99  fof(f70,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f43,f69])).
% 3.57/0.99  
% 3.57/0.99  fof(f82,plain,(
% 3.57/0.99    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f60,f70,f71,f71,f71])).
% 3.57/0.99  
% 3.57/0.99  fof(f84,plain,(
% 3.57/0.99    ( ! [X1] : (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) )),
% 3.57/0.99    inference(equality_resolution,[],[f82])).
% 3.57/0.99  
% 3.57/0.99  fof(f11,axiom,(
% 3.57/0.99    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f47,plain,(
% 3.57/0.99    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f11])).
% 3.57/0.99  
% 3.57/0.99  fof(f22,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f58,plain,(
% 3.57/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f22])).
% 3.57/0.99  
% 3.57/0.99  fof(f15,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f51,plain,(
% 3.57/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f15])).
% 3.57/0.99  
% 3.57/0.99  fof(f72,plain,(
% 3.57/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f51,f68,f57,f67])).
% 3.57/0.99  
% 3.57/0.99  fof(f80,plain,(
% 3.57/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f58,f72])).
% 3.57/0.99  
% 3.57/0.99  fof(f3,axiom,(
% 3.57/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f29,plain,(
% 3.57/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.57/0.99    inference(rectify,[],[f3])).
% 3.57/0.99  
% 3.57/0.99  fof(f39,plain,(
% 3.57/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f29])).
% 3.57/0.99  
% 3.57/0.99  fof(f75,plain,(
% 3.57/0.99    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 3.57/0.99    inference(definition_unfolding,[],[f39,f69])).
% 3.57/0.99  
% 3.57/0.99  fof(f2,axiom,(
% 3.57/0.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f28,plain,(
% 3.57/0.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.57/0.99    inference(rectify,[],[f2])).
% 3.57/0.99  
% 3.57/0.99  fof(f38,plain,(
% 3.57/0.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f28])).
% 3.57/0.99  
% 3.57/0.99  fof(f74,plain,(
% 3.57/0.99    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.57/0.99    inference(definition_unfolding,[],[f38,f68])).
% 3.57/0.99  
% 3.57/0.99  fof(f13,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f49,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f13])).
% 3.57/0.99  
% 3.57/0.99  fof(f79,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f49,f66,f66])).
% 3.57/0.99  
% 3.57/0.99  cnf(c_16,negated_conjecture,
% 3.57/0.99      ( k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5,plain,
% 3.57/0.99      ( v1_xboole_0(X0)
% 3.57/0.99      | ~ v1_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 3.57/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_148,plain,
% 3.57/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.57/0.99      | v1_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_463,plain,
% 3.57/0.99      ( v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = iProver_top
% 3.57/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_16,c_148]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1,plain,
% 3.57/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_34,plain,
% 3.57/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5963,plain,
% 3.57/0.99      ( v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_463,c_34]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_0,plain,
% 3.57/0.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.57/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_492,plain,
% 3.57/0.99      ( v1_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) != iProver_top
% 3.57/0.99      | v1_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_0,c_148]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10289,plain,
% 3.57/0.99      ( v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_5963,c_492]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4,plain,
% 3.57/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5718,plain,
% 3.57/0.99      ( ~ v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
% 3.57/0.99      | k1_xboole_0 = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5719,plain,
% 3.57/0.99      ( k1_xboole_0 = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)
% 3.57/0.99      | v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_5718]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5721,plain,
% 3.57/0.99      ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 3.57/0.99      | v1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_5719]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_67,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_281,plain,
% 3.57/0.99      ( X0 != X1 | X0 = k1_xboole_0 | k1_xboole_0 != X1 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_67]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_457,plain,
% 3.57/0.99      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1
% 3.57/0.99      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 != X1 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_281]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1097,plain,
% 3.57/0.99      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)
% 3.57/0.99      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_457]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1098,plain,
% 3.57/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 3.57/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1097]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14,plain,
% 3.57/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10,plain,
% 3.57/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_12,plain,
% 3.57/0.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.57/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3,plain,
% 3.57/0.99      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2,plain,
% 3.57/0.99      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_167,plain,
% 3.57/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_3,c_2,c_10]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_189,plain,
% 3.57/0.99      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_14,c_10,c_12,c_167]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_201,plain,
% 3.57/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_189]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_11,plain,
% 3.57/0.99      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_20,plain,
% 3.57/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(contradiction,plain,
% 3.57/0.99      ( $false ),
% 3.57/0.99      inference(minisat,[status(thm)],[c_10289,c_5721,c_1098,c_201,c_20]) ).
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  ------                               Statistics
% 3.57/0.99  
% 3.57/0.99  ------ Selected
% 3.57/0.99  
% 3.57/0.99  total_time:                             0.401
% 3.57/0.99  
%------------------------------------------------------------------------------
