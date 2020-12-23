%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:12 EST 2020

% Result     : Theorem 55.22s
% Output     : CNFRefutation 55.22s
% Verified   : 
% Statistics : Number of formulae       :  182 (43467 expanded)
%              Number of clauses        :  116 (8008 expanded)
%              Number of leaves         :   22 (13110 expanded)
%              Depth                    :   44
%              Number of atoms          :  189 (43488 expanded)
%              Number of equality atoms :  188 (43487 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f39,f58,f54,f56])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f38,f58,f54,f57])).

fof(f22,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f72,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f37,f55,f55])).

fof(f23,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f23])).

fof(f26,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f24])).

fof(f28,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
   => k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28])).

fof(f53,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f53,f58,f62])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f31,f59])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))))) ),
    inference(definition_unfolding,[],[f32,f58,f58,f60])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f30,f59])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f50,f60,f62,f62,f62])).

fof(f74,plain,(
    ! [X1] : k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f71])).

cnf(c_9,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1418,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_12,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_457,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_6,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_392,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6,c_13])).

cnf(c_2,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_404,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1)))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_138,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_135,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_38,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_5,c_12])).

cnf(c_142,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_135,c_38])).

cnf(c_247,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_138,c_142])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_255,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_247,c_3])).

cnf(c_267,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_255,c_142])).

cnf(c_272,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_267])).

cnf(c_262,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_4,c_255])).

cnf(c_1962,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_272,c_262])).

cnf(c_271,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_267])).

cnf(c_265,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_255,c_255])).

cnf(c_575,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_265,c_4])).

cnf(c_3210,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_271,c_575])).

cnf(c_264,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_142,c_255])).

cnf(c_552,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_264,c_4])).

cnf(c_2692,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_552,c_552])).

cnf(c_3328,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_3210,c_2692])).

cnf(c_15413,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1)),X0))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_404,c_1962,c_3328])).

cnf(c_15429,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k1_xboole_0,sK1))) ),
    inference(superposition,[status(thm)],[c_392,c_15413])).

cnf(c_15440,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_15429,c_12,c_38])).

cnf(c_406,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k5_enumset1(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X1)) ),
    inference(superposition,[status(thm)],[c_2,c_2])).

cnf(c_1916,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3,c_272])).

cnf(c_2017,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1916,c_264])).

cnf(c_149,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_4,c_142])).

cnf(c_2212,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_2017,c_149])).

cnf(c_2237,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_2212,c_3])).

cnf(c_2016,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1916,c_265])).

cnf(c_2094,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_2016])).

cnf(c_7465,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2237,c_2094])).

cnf(c_7584,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_7465,c_2094])).

cnf(c_2020,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1916,c_271])).

cnf(c_152,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_142,c_4])).

cnf(c_154,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_152,c_4])).

cnf(c_804,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_154,c_265])).

cnf(c_15119,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,X2)),X0) ),
    inference(superposition,[status(thm)],[c_2020,c_804])).

cnf(c_2168,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_2017])).

cnf(c_855,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_262,c_262])).

cnf(c_9769,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,X2)),X0) ),
    inference(superposition,[status(thm)],[c_2168,c_855])).

cnf(c_2202,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_272,c_2017])).

cnf(c_2241,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2202,c_4])).

cnf(c_9771,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X3)),X0) ),
    inference(superposition,[status(thm)],[c_2241,c_855])).

cnf(c_9499,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3) ),
    inference(superposition,[status(thm)],[c_2241,c_552])).

cnf(c_836,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_142,c_262])).

cnf(c_9533,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X3)),X0) ),
    inference(superposition,[status(thm)],[c_2241,c_836])).

cnf(c_2189,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_2017])).

cnf(c_8843,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_2189,c_575])).

cnf(c_1990,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_1916])).

cnf(c_5295,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1990,c_804])).

cnf(c_273,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_267])).

cnf(c_4767,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_273,c_1990])).

cnf(c_4771,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_4,c_1990])).

cnf(c_4836,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
    inference(superposition,[status(thm)],[c_1990,c_4])).

cnf(c_2356,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_273,c_1916])).

cnf(c_2382,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_273,c_1916])).

cnf(c_2404,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_2382,c_2020])).

cnf(c_2424,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_2356,c_2404])).

cnf(c_4870,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X2,X0),k5_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_4836,c_1916,c_2424,c_3328])).

cnf(c_4935,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))) ),
    inference(demodulation,[status(thm)],[c_4767,c_4771,c_4870])).

cnf(c_5411,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X2,X1))) ),
    inference(light_normalisation,[status(thm)],[c_5295,c_4935])).

cnf(c_8874,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_8843,c_5411])).

cnf(c_9544,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
    inference(light_normalisation,[status(thm)],[c_9533,c_8874])).

cnf(c_9577,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X0,X3))) ),
    inference(demodulation,[status(thm)],[c_9499,c_9544])).

cnf(c_9980,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(light_normalisation,[status(thm)],[c_9771,c_9577])).

cnf(c_9981,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_9769,c_9980])).

cnf(c_15187,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X3,X2))) ),
    inference(light_normalisation,[status(thm)],[c_15119,c_9981])).

cnf(c_17935,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),X1)) ),
    inference(demodulation,[status(thm)],[c_406,c_1962,c_3328,c_7584,c_15187])).

cnf(c_17936,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1)))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),X1)) ),
    inference(demodulation,[status(thm)],[c_17935,c_1962,c_3328])).

cnf(c_18140,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(sK1,k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_15440,c_17936])).

cnf(c_18233,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) ),
    inference(demodulation,[status(thm)],[c_18140,c_255])).

cnf(c_20450,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[status(thm)],[c_6,c_18233])).

cnf(c_20468,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) = k3_tarski(k5_enumset1(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_20450,c_392])).

cnf(c_402,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X0)))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_2])).

cnf(c_407,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_402,c_5,c_12,c_38])).

cnf(c_20469,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_20468,c_38,c_407])).

cnf(c_20474,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_6,c_20469])).

cnf(c_48153,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1))) = sK1 ),
    inference(demodulation,[status(thm)],[c_457,c_20474])).

cnf(c_395,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_413,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_395,c_142])).

cnf(c_27869,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_15440,c_413])).

cnf(c_48145,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(demodulation,[status(thm)],[c_457,c_27869])).

cnf(c_400,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,X1))))))) = k3_tarski(k5_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_142,c_2])).

cnf(c_33253,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))))) = k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_27869,c_400])).

cnf(c_33272,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) = k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_6,c_33253])).

cnf(c_33290,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k1_xboole_0)))) = k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_33272,c_392])).

cnf(c_33291,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_33290,c_3,c_12])).

cnf(c_48162,plain,
    ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_457,c_33291])).

cnf(c_49729,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_6,c_48162])).

cnf(c_51077,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_457,c_49729])).

cnf(c_57094,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_48145,c_51077])).

cnf(c_57401,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1),k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1),k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_48153,c_48153,c_57094])).

cnf(c_57402,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_57401,c_264])).

cnf(c_57403,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_1418,c_57402])).

cnf(c_48883,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1418,c_392])).

cnf(c_57407,plain,
    ( sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_57403,c_48883])).

cnf(c_57408,plain,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_57407,c_57402])).

cnf(c_2446,plain,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_407])).

cnf(c_63011,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_57408,c_2446])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11,c_5,c_9,c_38])).

cnf(c_41,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63011,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:47:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.22/7.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.22/7.49  
% 55.22/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.22/7.49  
% 55.22/7.49  ------  iProver source info
% 55.22/7.49  
% 55.22/7.49  git: date: 2020-06-30 10:37:57 +0100
% 55.22/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.22/7.49  git: non_committed_changes: false
% 55.22/7.49  git: last_make_outside_of_git: false
% 55.22/7.49  
% 55.22/7.49  ------ 
% 55.22/7.49  
% 55.22/7.49  ------ Input Options
% 55.22/7.49  
% 55.22/7.49  --out_options                           all
% 55.22/7.49  --tptp_safe_out                         true
% 55.22/7.49  --problem_path                          ""
% 55.22/7.49  --include_path                          ""
% 55.22/7.49  --clausifier                            res/vclausify_rel
% 55.22/7.49  --clausifier_options                    ""
% 55.22/7.49  --stdin                                 false
% 55.22/7.49  --stats_out                             all
% 55.22/7.49  
% 55.22/7.49  ------ General Options
% 55.22/7.49  
% 55.22/7.49  --fof                                   false
% 55.22/7.49  --time_out_real                         305.
% 55.22/7.49  --time_out_virtual                      -1.
% 55.22/7.49  --symbol_type_check                     false
% 55.22/7.49  --clausify_out                          false
% 55.22/7.49  --sig_cnt_out                           false
% 55.22/7.49  --trig_cnt_out                          false
% 55.22/7.49  --trig_cnt_out_tolerance                1.
% 55.22/7.49  --trig_cnt_out_sk_spl                   false
% 55.22/7.49  --abstr_cl_out                          false
% 55.22/7.49  
% 55.22/7.49  ------ Global Options
% 55.22/7.49  
% 55.22/7.49  --schedule                              default
% 55.22/7.49  --add_important_lit                     false
% 55.22/7.49  --prop_solver_per_cl                    1000
% 55.22/7.49  --min_unsat_core                        false
% 55.22/7.49  --soft_assumptions                      false
% 55.22/7.49  --soft_lemma_size                       3
% 55.22/7.49  --prop_impl_unit_size                   0
% 55.22/7.49  --prop_impl_unit                        []
% 55.22/7.49  --share_sel_clauses                     true
% 55.22/7.49  --reset_solvers                         false
% 55.22/7.49  --bc_imp_inh                            [conj_cone]
% 55.22/7.49  --conj_cone_tolerance                   3.
% 55.22/7.49  --extra_neg_conj                        none
% 55.22/7.49  --large_theory_mode                     true
% 55.22/7.49  --prolific_symb_bound                   200
% 55.22/7.49  --lt_threshold                          2000
% 55.22/7.49  --clause_weak_htbl                      true
% 55.22/7.49  --gc_record_bc_elim                     false
% 55.22/7.49  
% 55.22/7.49  ------ Preprocessing Options
% 55.22/7.49  
% 55.22/7.49  --preprocessing_flag                    true
% 55.22/7.49  --time_out_prep_mult                    0.1
% 55.22/7.49  --splitting_mode                        input
% 55.22/7.49  --splitting_grd                         true
% 55.22/7.49  --splitting_cvd                         false
% 55.22/7.49  --splitting_cvd_svl                     false
% 55.22/7.49  --splitting_nvd                         32
% 55.22/7.49  --sub_typing                            true
% 55.22/7.49  --prep_gs_sim                           true
% 55.22/7.49  --prep_unflatten                        true
% 55.22/7.49  --prep_res_sim                          true
% 55.22/7.49  --prep_upred                            true
% 55.22/7.49  --prep_sem_filter                       exhaustive
% 55.22/7.49  --prep_sem_filter_out                   false
% 55.22/7.49  --pred_elim                             true
% 55.22/7.49  --res_sim_input                         true
% 55.22/7.49  --eq_ax_congr_red                       true
% 55.22/7.49  --pure_diseq_elim                       true
% 55.22/7.49  --brand_transform                       false
% 55.22/7.49  --non_eq_to_eq                          false
% 55.22/7.49  --prep_def_merge                        true
% 55.22/7.49  --prep_def_merge_prop_impl              false
% 55.22/7.49  --prep_def_merge_mbd                    true
% 55.22/7.49  --prep_def_merge_tr_red                 false
% 55.22/7.49  --prep_def_merge_tr_cl                  false
% 55.22/7.49  --smt_preprocessing                     true
% 55.22/7.49  --smt_ac_axioms                         fast
% 55.22/7.49  --preprocessed_out                      false
% 55.22/7.49  --preprocessed_stats                    false
% 55.22/7.49  
% 55.22/7.49  ------ Abstraction refinement Options
% 55.22/7.49  
% 55.22/7.49  --abstr_ref                             []
% 55.22/7.49  --abstr_ref_prep                        false
% 55.22/7.49  --abstr_ref_until_sat                   false
% 55.22/7.49  --abstr_ref_sig_restrict                funpre
% 55.22/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.22/7.49  --abstr_ref_under                       []
% 55.22/7.49  
% 55.22/7.49  ------ SAT Options
% 55.22/7.49  
% 55.22/7.49  --sat_mode                              false
% 55.22/7.49  --sat_fm_restart_options                ""
% 55.22/7.49  --sat_gr_def                            false
% 55.22/7.49  --sat_epr_types                         true
% 55.22/7.49  --sat_non_cyclic_types                  false
% 55.22/7.49  --sat_finite_models                     false
% 55.22/7.49  --sat_fm_lemmas                         false
% 55.22/7.49  --sat_fm_prep                           false
% 55.22/7.49  --sat_fm_uc_incr                        true
% 55.22/7.49  --sat_out_model                         small
% 55.22/7.49  --sat_out_clauses                       false
% 55.22/7.49  
% 55.22/7.49  ------ QBF Options
% 55.22/7.49  
% 55.22/7.49  --qbf_mode                              false
% 55.22/7.49  --qbf_elim_univ                         false
% 55.22/7.49  --qbf_dom_inst                          none
% 55.22/7.49  --qbf_dom_pre_inst                      false
% 55.22/7.49  --qbf_sk_in                             false
% 55.22/7.49  --qbf_pred_elim                         true
% 55.22/7.49  --qbf_split                             512
% 55.22/7.49  
% 55.22/7.49  ------ BMC1 Options
% 55.22/7.49  
% 55.22/7.49  --bmc1_incremental                      false
% 55.22/7.49  --bmc1_axioms                           reachable_all
% 55.22/7.49  --bmc1_min_bound                        0
% 55.22/7.49  --bmc1_max_bound                        -1
% 55.22/7.49  --bmc1_max_bound_default                -1
% 55.22/7.49  --bmc1_symbol_reachability              true
% 55.22/7.49  --bmc1_property_lemmas                  false
% 55.22/7.49  --bmc1_k_induction                      false
% 55.22/7.49  --bmc1_non_equiv_states                 false
% 55.22/7.49  --bmc1_deadlock                         false
% 55.22/7.49  --bmc1_ucm                              false
% 55.22/7.49  --bmc1_add_unsat_core                   none
% 55.22/7.49  --bmc1_unsat_core_children              false
% 55.22/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.22/7.49  --bmc1_out_stat                         full
% 55.22/7.49  --bmc1_ground_init                      false
% 55.22/7.49  --bmc1_pre_inst_next_state              false
% 55.22/7.49  --bmc1_pre_inst_state                   false
% 55.22/7.49  --bmc1_pre_inst_reach_state             false
% 55.22/7.49  --bmc1_out_unsat_core                   false
% 55.22/7.49  --bmc1_aig_witness_out                  false
% 55.22/7.49  --bmc1_verbose                          false
% 55.22/7.49  --bmc1_dump_clauses_tptp                false
% 55.22/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.22/7.49  --bmc1_dump_file                        -
% 55.22/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.22/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.22/7.49  --bmc1_ucm_extend_mode                  1
% 55.22/7.49  --bmc1_ucm_init_mode                    2
% 55.22/7.49  --bmc1_ucm_cone_mode                    none
% 55.22/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.22/7.49  --bmc1_ucm_relax_model                  4
% 55.22/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.22/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.22/7.49  --bmc1_ucm_layered_model                none
% 55.22/7.49  --bmc1_ucm_max_lemma_size               10
% 55.22/7.49  
% 55.22/7.49  ------ AIG Options
% 55.22/7.49  
% 55.22/7.49  --aig_mode                              false
% 55.22/7.49  
% 55.22/7.49  ------ Instantiation Options
% 55.22/7.49  
% 55.22/7.49  --instantiation_flag                    true
% 55.22/7.49  --inst_sos_flag                         true
% 55.22/7.49  --inst_sos_phase                        true
% 55.22/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.22/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.22/7.49  --inst_lit_sel_side                     num_symb
% 55.22/7.49  --inst_solver_per_active                1400
% 55.22/7.49  --inst_solver_calls_frac                1.
% 55.22/7.49  --inst_passive_queue_type               priority_queues
% 55.22/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.22/7.49  --inst_passive_queues_freq              [25;2]
% 55.22/7.49  --inst_dismatching                      true
% 55.22/7.49  --inst_eager_unprocessed_to_passive     true
% 55.22/7.49  --inst_prop_sim_given                   true
% 55.22/7.49  --inst_prop_sim_new                     false
% 55.22/7.49  --inst_subs_new                         false
% 55.22/7.49  --inst_eq_res_simp                      false
% 55.22/7.49  --inst_subs_given                       false
% 55.22/7.49  --inst_orphan_elimination               true
% 55.22/7.49  --inst_learning_loop_flag               true
% 55.22/7.49  --inst_learning_start                   3000
% 55.22/7.49  --inst_learning_factor                  2
% 55.22/7.49  --inst_start_prop_sim_after_learn       3
% 55.22/7.49  --inst_sel_renew                        solver
% 55.22/7.49  --inst_lit_activity_flag                true
% 55.22/7.49  --inst_restr_to_given                   false
% 55.22/7.49  --inst_activity_threshold               500
% 55.22/7.49  --inst_out_proof                        true
% 55.22/7.49  
% 55.22/7.49  ------ Resolution Options
% 55.22/7.49  
% 55.22/7.49  --resolution_flag                       true
% 55.22/7.49  --res_lit_sel                           adaptive
% 55.22/7.49  --res_lit_sel_side                      none
% 55.22/7.49  --res_ordering                          kbo
% 55.22/7.49  --res_to_prop_solver                    active
% 55.22/7.49  --res_prop_simpl_new                    false
% 55.22/7.49  --res_prop_simpl_given                  true
% 55.22/7.49  --res_passive_queue_type                priority_queues
% 55.22/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.22/7.49  --res_passive_queues_freq               [15;5]
% 55.22/7.49  --res_forward_subs                      full
% 55.22/7.49  --res_backward_subs                     full
% 55.22/7.49  --res_forward_subs_resolution           true
% 55.22/7.49  --res_backward_subs_resolution          true
% 55.22/7.49  --res_orphan_elimination                true
% 55.22/7.49  --res_time_limit                        2.
% 55.22/7.49  --res_out_proof                         true
% 55.22/7.49  
% 55.22/7.49  ------ Superposition Options
% 55.22/7.49  
% 55.22/7.49  --superposition_flag                    true
% 55.22/7.49  --sup_passive_queue_type                priority_queues
% 55.22/7.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.22/7.49  --sup_passive_queues_freq               [8;1;4]
% 55.22/7.49  --demod_completeness_check              fast
% 55.22/7.49  --demod_use_ground                      true
% 55.22/7.49  --sup_to_prop_solver                    passive
% 55.22/7.49  --sup_prop_simpl_new                    true
% 55.22/7.49  --sup_prop_simpl_given                  true
% 55.22/7.49  --sup_fun_splitting                     true
% 55.22/7.49  --sup_smt_interval                      50000
% 55.22/7.49  
% 55.22/7.49  ------ Superposition Simplification Setup
% 55.22/7.49  
% 55.22/7.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.22/7.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.22/7.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.22/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.22/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 55.22/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.22/7.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.22/7.49  --sup_immed_triv                        [TrivRules]
% 55.22/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.22/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.22/7.49  --sup_immed_bw_main                     []
% 55.22/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.22/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.22/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.22/7.49  --sup_input_bw                          []
% 55.22/7.49  
% 55.22/7.49  ------ Combination Options
% 55.22/7.49  
% 55.22/7.49  --comb_res_mult                         3
% 55.22/7.49  --comb_sup_mult                         2
% 55.22/7.49  --comb_inst_mult                        10
% 55.22/7.49  
% 55.22/7.49  ------ Debug Options
% 55.22/7.49  
% 55.22/7.49  --dbg_backtrace                         false
% 55.22/7.49  --dbg_dump_prop_clauses                 false
% 55.22/7.49  --dbg_dump_prop_clauses_file            -
% 55.22/7.49  --dbg_out_stat                          false
% 55.22/7.49  ------ Parsing...
% 55.22/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.22/7.49  
% 55.22/7.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 55.22/7.49  
% 55.22/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.22/7.49  
% 55.22/7.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 55.22/7.49  ------ Proving...
% 55.22/7.49  ------ Problem Properties 
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  clauses                                 14
% 55.22/7.49  conjectures                             1
% 55.22/7.49  EPR                                     0
% 55.22/7.49  Horn                                    13
% 55.22/7.49  unary                                   13
% 55.22/7.49  binary                                  1
% 55.22/7.49  lits                                    15
% 55.22/7.49  lits eq                                 15
% 55.22/7.49  fd_pure                                 0
% 55.22/7.49  fd_pseudo                               0
% 55.22/7.49  fd_cond                                 0
% 55.22/7.49  fd_pseudo_cond                          1
% 55.22/7.49  AC symbols                              0
% 55.22/7.49  
% 55.22/7.49  ------ Schedule dynamic 5 is on 
% 55.22/7.49  
% 55.22/7.49  ------ pure equality problem: resolution off 
% 55.22/7.49  
% 55.22/7.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  ------ 
% 55.22/7.49  Current options:
% 55.22/7.49  ------ 
% 55.22/7.49  
% 55.22/7.49  ------ Input Options
% 55.22/7.49  
% 55.22/7.49  --out_options                           all
% 55.22/7.49  --tptp_safe_out                         true
% 55.22/7.49  --problem_path                          ""
% 55.22/7.49  --include_path                          ""
% 55.22/7.49  --clausifier                            res/vclausify_rel
% 55.22/7.49  --clausifier_options                    ""
% 55.22/7.49  --stdin                                 false
% 55.22/7.49  --stats_out                             all
% 55.22/7.49  
% 55.22/7.49  ------ General Options
% 55.22/7.49  
% 55.22/7.49  --fof                                   false
% 55.22/7.49  --time_out_real                         305.
% 55.22/7.49  --time_out_virtual                      -1.
% 55.22/7.49  --symbol_type_check                     false
% 55.22/7.49  --clausify_out                          false
% 55.22/7.49  --sig_cnt_out                           false
% 55.22/7.49  --trig_cnt_out                          false
% 55.22/7.49  --trig_cnt_out_tolerance                1.
% 55.22/7.49  --trig_cnt_out_sk_spl                   false
% 55.22/7.49  --abstr_cl_out                          false
% 55.22/7.49  
% 55.22/7.49  ------ Global Options
% 55.22/7.49  
% 55.22/7.49  --schedule                              default
% 55.22/7.49  --add_important_lit                     false
% 55.22/7.49  --prop_solver_per_cl                    1000
% 55.22/7.49  --min_unsat_core                        false
% 55.22/7.49  --soft_assumptions                      false
% 55.22/7.49  --soft_lemma_size                       3
% 55.22/7.49  --prop_impl_unit_size                   0
% 55.22/7.49  --prop_impl_unit                        []
% 55.22/7.49  --share_sel_clauses                     true
% 55.22/7.49  --reset_solvers                         false
% 55.22/7.49  --bc_imp_inh                            [conj_cone]
% 55.22/7.49  --conj_cone_tolerance                   3.
% 55.22/7.49  --extra_neg_conj                        none
% 55.22/7.49  --large_theory_mode                     true
% 55.22/7.49  --prolific_symb_bound                   200
% 55.22/7.49  --lt_threshold                          2000
% 55.22/7.49  --clause_weak_htbl                      true
% 55.22/7.49  --gc_record_bc_elim                     false
% 55.22/7.49  
% 55.22/7.49  ------ Preprocessing Options
% 55.22/7.49  
% 55.22/7.49  --preprocessing_flag                    true
% 55.22/7.49  --time_out_prep_mult                    0.1
% 55.22/7.49  --splitting_mode                        input
% 55.22/7.49  --splitting_grd                         true
% 55.22/7.49  --splitting_cvd                         false
% 55.22/7.49  --splitting_cvd_svl                     false
% 55.22/7.49  --splitting_nvd                         32
% 55.22/7.49  --sub_typing                            true
% 55.22/7.49  --prep_gs_sim                           true
% 55.22/7.49  --prep_unflatten                        true
% 55.22/7.49  --prep_res_sim                          true
% 55.22/7.49  --prep_upred                            true
% 55.22/7.49  --prep_sem_filter                       exhaustive
% 55.22/7.49  --prep_sem_filter_out                   false
% 55.22/7.49  --pred_elim                             true
% 55.22/7.49  --res_sim_input                         true
% 55.22/7.49  --eq_ax_congr_red                       true
% 55.22/7.49  --pure_diseq_elim                       true
% 55.22/7.49  --brand_transform                       false
% 55.22/7.49  --non_eq_to_eq                          false
% 55.22/7.49  --prep_def_merge                        true
% 55.22/7.49  --prep_def_merge_prop_impl              false
% 55.22/7.49  --prep_def_merge_mbd                    true
% 55.22/7.49  --prep_def_merge_tr_red                 false
% 55.22/7.49  --prep_def_merge_tr_cl                  false
% 55.22/7.49  --smt_preprocessing                     true
% 55.22/7.49  --smt_ac_axioms                         fast
% 55.22/7.49  --preprocessed_out                      false
% 55.22/7.49  --preprocessed_stats                    false
% 55.22/7.49  
% 55.22/7.49  ------ Abstraction refinement Options
% 55.22/7.49  
% 55.22/7.49  --abstr_ref                             []
% 55.22/7.49  --abstr_ref_prep                        false
% 55.22/7.49  --abstr_ref_until_sat                   false
% 55.22/7.49  --abstr_ref_sig_restrict                funpre
% 55.22/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.22/7.49  --abstr_ref_under                       []
% 55.22/7.49  
% 55.22/7.49  ------ SAT Options
% 55.22/7.49  
% 55.22/7.49  --sat_mode                              false
% 55.22/7.49  --sat_fm_restart_options                ""
% 55.22/7.49  --sat_gr_def                            false
% 55.22/7.49  --sat_epr_types                         true
% 55.22/7.49  --sat_non_cyclic_types                  false
% 55.22/7.49  --sat_finite_models                     false
% 55.22/7.49  --sat_fm_lemmas                         false
% 55.22/7.49  --sat_fm_prep                           false
% 55.22/7.49  --sat_fm_uc_incr                        true
% 55.22/7.49  --sat_out_model                         small
% 55.22/7.49  --sat_out_clauses                       false
% 55.22/7.49  
% 55.22/7.49  ------ QBF Options
% 55.22/7.49  
% 55.22/7.49  --qbf_mode                              false
% 55.22/7.49  --qbf_elim_univ                         false
% 55.22/7.49  --qbf_dom_inst                          none
% 55.22/7.49  --qbf_dom_pre_inst                      false
% 55.22/7.49  --qbf_sk_in                             false
% 55.22/7.49  --qbf_pred_elim                         true
% 55.22/7.49  --qbf_split                             512
% 55.22/7.49  
% 55.22/7.49  ------ BMC1 Options
% 55.22/7.49  
% 55.22/7.49  --bmc1_incremental                      false
% 55.22/7.49  --bmc1_axioms                           reachable_all
% 55.22/7.49  --bmc1_min_bound                        0
% 55.22/7.49  --bmc1_max_bound                        -1
% 55.22/7.49  --bmc1_max_bound_default                -1
% 55.22/7.49  --bmc1_symbol_reachability              true
% 55.22/7.49  --bmc1_property_lemmas                  false
% 55.22/7.49  --bmc1_k_induction                      false
% 55.22/7.49  --bmc1_non_equiv_states                 false
% 55.22/7.49  --bmc1_deadlock                         false
% 55.22/7.49  --bmc1_ucm                              false
% 55.22/7.49  --bmc1_add_unsat_core                   none
% 55.22/7.49  --bmc1_unsat_core_children              false
% 55.22/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.22/7.49  --bmc1_out_stat                         full
% 55.22/7.49  --bmc1_ground_init                      false
% 55.22/7.49  --bmc1_pre_inst_next_state              false
% 55.22/7.49  --bmc1_pre_inst_state                   false
% 55.22/7.49  --bmc1_pre_inst_reach_state             false
% 55.22/7.49  --bmc1_out_unsat_core                   false
% 55.22/7.49  --bmc1_aig_witness_out                  false
% 55.22/7.49  --bmc1_verbose                          false
% 55.22/7.49  --bmc1_dump_clauses_tptp                false
% 55.22/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.22/7.49  --bmc1_dump_file                        -
% 55.22/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.22/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.22/7.49  --bmc1_ucm_extend_mode                  1
% 55.22/7.49  --bmc1_ucm_init_mode                    2
% 55.22/7.49  --bmc1_ucm_cone_mode                    none
% 55.22/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.22/7.49  --bmc1_ucm_relax_model                  4
% 55.22/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.22/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.22/7.49  --bmc1_ucm_layered_model                none
% 55.22/7.49  --bmc1_ucm_max_lemma_size               10
% 55.22/7.49  
% 55.22/7.49  ------ AIG Options
% 55.22/7.49  
% 55.22/7.49  --aig_mode                              false
% 55.22/7.49  
% 55.22/7.49  ------ Instantiation Options
% 55.22/7.49  
% 55.22/7.49  --instantiation_flag                    true
% 55.22/7.49  --inst_sos_flag                         true
% 55.22/7.49  --inst_sos_phase                        true
% 55.22/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.22/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.22/7.49  --inst_lit_sel_side                     none
% 55.22/7.49  --inst_solver_per_active                1400
% 55.22/7.49  --inst_solver_calls_frac                1.
% 55.22/7.49  --inst_passive_queue_type               priority_queues
% 55.22/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.22/7.49  --inst_passive_queues_freq              [25;2]
% 55.22/7.49  --inst_dismatching                      true
% 55.22/7.49  --inst_eager_unprocessed_to_passive     true
% 55.22/7.49  --inst_prop_sim_given                   true
% 55.22/7.49  --inst_prop_sim_new                     false
% 55.22/7.49  --inst_subs_new                         false
% 55.22/7.49  --inst_eq_res_simp                      false
% 55.22/7.49  --inst_subs_given                       false
% 55.22/7.49  --inst_orphan_elimination               true
% 55.22/7.49  --inst_learning_loop_flag               true
% 55.22/7.49  --inst_learning_start                   3000
% 55.22/7.49  --inst_learning_factor                  2
% 55.22/7.49  --inst_start_prop_sim_after_learn       3
% 55.22/7.49  --inst_sel_renew                        solver
% 55.22/7.49  --inst_lit_activity_flag                true
% 55.22/7.49  --inst_restr_to_given                   false
% 55.22/7.49  --inst_activity_threshold               500
% 55.22/7.49  --inst_out_proof                        true
% 55.22/7.49  
% 55.22/7.49  ------ Resolution Options
% 55.22/7.49  
% 55.22/7.49  --resolution_flag                       false
% 55.22/7.49  --res_lit_sel                           adaptive
% 55.22/7.49  --res_lit_sel_side                      none
% 55.22/7.49  --res_ordering                          kbo
% 55.22/7.49  --res_to_prop_solver                    active
% 55.22/7.49  --res_prop_simpl_new                    false
% 55.22/7.49  --res_prop_simpl_given                  true
% 55.22/7.49  --res_passive_queue_type                priority_queues
% 55.22/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.22/7.49  --res_passive_queues_freq               [15;5]
% 55.22/7.49  --res_forward_subs                      full
% 55.22/7.49  --res_backward_subs                     full
% 55.22/7.49  --res_forward_subs_resolution           true
% 55.22/7.49  --res_backward_subs_resolution          true
% 55.22/7.49  --res_orphan_elimination                true
% 55.22/7.49  --res_time_limit                        2.
% 55.22/7.49  --res_out_proof                         true
% 55.22/7.49  
% 55.22/7.49  ------ Superposition Options
% 55.22/7.49  
% 55.22/7.49  --superposition_flag                    true
% 55.22/7.49  --sup_passive_queue_type                priority_queues
% 55.22/7.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.22/7.49  --sup_passive_queues_freq               [8;1;4]
% 55.22/7.49  --demod_completeness_check              fast
% 55.22/7.49  --demod_use_ground                      true
% 55.22/7.49  --sup_to_prop_solver                    passive
% 55.22/7.49  --sup_prop_simpl_new                    true
% 55.22/7.49  --sup_prop_simpl_given                  true
% 55.22/7.49  --sup_fun_splitting                     true
% 55.22/7.49  --sup_smt_interval                      50000
% 55.22/7.49  
% 55.22/7.49  ------ Superposition Simplification Setup
% 55.22/7.49  
% 55.22/7.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.22/7.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.22/7.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.22/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.22/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 55.22/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.22/7.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.22/7.49  --sup_immed_triv                        [TrivRules]
% 55.22/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.22/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.22/7.49  --sup_immed_bw_main                     []
% 55.22/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.22/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.22/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.22/7.49  --sup_input_bw                          []
% 55.22/7.49  
% 55.22/7.49  ------ Combination Options
% 55.22/7.49  
% 55.22/7.49  --comb_res_mult                         3
% 55.22/7.49  --comb_sup_mult                         2
% 55.22/7.49  --comb_inst_mult                        10
% 55.22/7.49  
% 55.22/7.49  ------ Debug Options
% 55.22/7.49  
% 55.22/7.49  --dbg_backtrace                         false
% 55.22/7.49  --dbg_dump_prop_clauses                 false
% 55.22/7.49  --dbg_dump_prop_clauses_file            -
% 55.22/7.49  --dbg_out_stat                          false
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  ------ Proving...
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  % SZS status Theorem for theBenchmark.p
% 55.22/7.49  
% 55.22/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 55.22/7.49  
% 55.22/7.49  fof(f19,axiom,(
% 55.22/7.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f48,plain,(
% 55.22/7.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f19])).
% 55.22/7.49  
% 55.22/7.49  fof(f10,axiom,(
% 55.22/7.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f39,plain,(
% 55.22/7.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f10])).
% 55.22/7.49  
% 55.22/7.49  fof(f20,axiom,(
% 55.22/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f49,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 55.22/7.49    inference(cnf_transformation,[],[f20])).
% 55.22/7.49  
% 55.22/7.49  fof(f14,axiom,(
% 55.22/7.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f43,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f14])).
% 55.22/7.49  
% 55.22/7.49  fof(f57,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 55.22/7.49    inference(definition_unfolding,[],[f43,f56])).
% 55.22/7.49  
% 55.22/7.49  fof(f58,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 55.22/7.49    inference(definition_unfolding,[],[f49,f57])).
% 55.22/7.49  
% 55.22/7.49  fof(f15,axiom,(
% 55.22/7.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f44,plain,(
% 55.22/7.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f15])).
% 55.22/7.49  
% 55.22/7.49  fof(f16,axiom,(
% 55.22/7.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f45,plain,(
% 55.22/7.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f16])).
% 55.22/7.49  
% 55.22/7.49  fof(f17,axiom,(
% 55.22/7.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f46,plain,(
% 55.22/7.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f17])).
% 55.22/7.49  
% 55.22/7.49  fof(f18,axiom,(
% 55.22/7.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f47,plain,(
% 55.22/7.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f18])).
% 55.22/7.49  
% 55.22/7.49  fof(f54,plain,(
% 55.22/7.49    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 55.22/7.49    inference(definition_unfolding,[],[f46,f47])).
% 55.22/7.49  
% 55.22/7.49  fof(f55,plain,(
% 55.22/7.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 55.22/7.49    inference(definition_unfolding,[],[f45,f54])).
% 55.22/7.49  
% 55.22/7.49  fof(f56,plain,(
% 55.22/7.49    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 55.22/7.49    inference(definition_unfolding,[],[f44,f55])).
% 55.22/7.49  
% 55.22/7.49  fof(f61,plain,(
% 55.22/7.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X6,X7)))) )),
% 55.22/7.49    inference(definition_unfolding,[],[f39,f58,f54,f56])).
% 55.22/7.49  
% 55.22/7.49  fof(f69,plain,(
% 55.22/7.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6)))) )),
% 55.22/7.49    inference(definition_unfolding,[],[f48,f61])).
% 55.22/7.49  
% 55.22/7.49  fof(f9,axiom,(
% 55.22/7.49    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f38,plain,(
% 55.22/7.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f9])).
% 55.22/7.49  
% 55.22/7.49  fof(f63,plain,(
% 55.22/7.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 55.22/7.49    inference(definition_unfolding,[],[f38,f58,f54,f57])).
% 55.22/7.49  
% 55.22/7.49  fof(f22,axiom,(
% 55.22/7.49    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f52,plain,(
% 55.22/7.49    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 55.22/7.49    inference(cnf_transformation,[],[f22])).
% 55.22/7.49  
% 55.22/7.49  fof(f13,axiom,(
% 55.22/7.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f42,plain,(
% 55.22/7.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f13])).
% 55.22/7.49  
% 55.22/7.49  fof(f62,plain,(
% 55.22/7.49    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 55.22/7.49    inference(definition_unfolding,[],[f42,f57])).
% 55.22/7.49  
% 55.22/7.49  fof(f72,plain,(
% 55.22/7.49    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 55.22/7.49    inference(definition_unfolding,[],[f52,f62])).
% 55.22/7.49  
% 55.22/7.49  fof(f8,axiom,(
% 55.22/7.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f37,plain,(
% 55.22/7.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f8])).
% 55.22/7.49  
% 55.22/7.49  fof(f66,plain,(
% 55.22/7.49    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 55.22/7.49    inference(definition_unfolding,[],[f37,f55,f55])).
% 55.22/7.49  
% 55.22/7.49  fof(f23,conjecture,(
% 55.22/7.49    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f24,negated_conjecture,(
% 55.22/7.49    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 55.22/7.49    inference(negated_conjecture,[],[f23])).
% 55.22/7.49  
% 55.22/7.49  fof(f26,plain,(
% 55.22/7.49    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0),
% 55.22/7.49    inference(ennf_transformation,[],[f24])).
% 55.22/7.49  
% 55.22/7.49  fof(f28,plain,(
% 55.22/7.49    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 => k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0),
% 55.22/7.49    introduced(choice_axiom,[])).
% 55.22/7.49  
% 55.22/7.49  fof(f29,plain,(
% 55.22/7.49    k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0),
% 55.22/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28])).
% 55.22/7.49  
% 55.22/7.49  fof(f53,plain,(
% 55.22/7.49    k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0),
% 55.22/7.49    inference(cnf_transformation,[],[f29])).
% 55.22/7.49  
% 55.22/7.49  fof(f73,plain,(
% 55.22/7.49    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 55.22/7.49    inference(definition_unfolding,[],[f53,f58,f62])).
% 55.22/7.49  
% 55.22/7.49  fof(f3,axiom,(
% 55.22/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f32,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 55.22/7.49    inference(cnf_transformation,[],[f3])).
% 55.22/7.49  
% 55.22/7.49  fof(f2,axiom,(
% 55.22/7.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f31,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.22/7.49    inference(cnf_transformation,[],[f2])).
% 55.22/7.49  
% 55.22/7.49  fof(f7,axiom,(
% 55.22/7.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f36,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 55.22/7.49    inference(cnf_transformation,[],[f7])).
% 55.22/7.49  
% 55.22/7.49  fof(f59,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 55.22/7.49    inference(definition_unfolding,[],[f36,f58])).
% 55.22/7.49  
% 55.22/7.49  fof(f60,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) )),
% 55.22/7.49    inference(definition_unfolding,[],[f31,f59])).
% 55.22/7.49  
% 55.22/7.49  fof(f65,plain,(
% 55.22/7.49    ( ! [X0,X1] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))))) )),
% 55.22/7.49    inference(definition_unfolding,[],[f32,f58,f58,f60])).
% 55.22/7.49  
% 55.22/7.49  fof(f5,axiom,(
% 55.22/7.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f34,plain,(
% 55.22/7.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f5])).
% 55.22/7.49  
% 55.22/7.49  fof(f6,axiom,(
% 55.22/7.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f35,plain,(
% 55.22/7.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 55.22/7.49    inference(cnf_transformation,[],[f6])).
% 55.22/7.49  
% 55.22/7.49  fof(f1,axiom,(
% 55.22/7.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f25,plain,(
% 55.22/7.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 55.22/7.49    inference(rectify,[],[f1])).
% 55.22/7.49  
% 55.22/7.49  fof(f30,plain,(
% 55.22/7.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 55.22/7.49    inference(cnf_transformation,[],[f25])).
% 55.22/7.49  
% 55.22/7.49  fof(f64,plain,(
% 55.22/7.49    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 55.22/7.49    inference(definition_unfolding,[],[f30,f59])).
% 55.22/7.49  
% 55.22/7.49  fof(f4,axiom,(
% 55.22/7.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f33,plain,(
% 55.22/7.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.22/7.49    inference(cnf_transformation,[],[f4])).
% 55.22/7.49  
% 55.22/7.49  fof(f21,axiom,(
% 55.22/7.49    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 55.22/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.22/7.49  
% 55.22/7.49  fof(f27,plain,(
% 55.22/7.49    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 55.22/7.49    inference(nnf_transformation,[],[f21])).
% 55.22/7.49  
% 55.22/7.49  fof(f50,plain,(
% 55.22/7.49    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 55.22/7.49    inference(cnf_transformation,[],[f27])).
% 55.22/7.49  
% 55.22/7.49  fof(f71,plain,(
% 55.22/7.49    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 55.22/7.49    inference(definition_unfolding,[],[f50,f60,f62,f62,f62])).
% 55.22/7.49  
% 55.22/7.49  fof(f74,plain,(
% 55.22/7.49    ( ! [X1] : (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) )),
% 55.22/7.49    inference(equality_resolution,[],[f71])).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 55.22/7.49      inference(cnf_transformation,[],[f69]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_0,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 55.22/7.49      inference(cnf_transformation,[],[f63]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_1418,plain,
% 55.22/7.49      ( k5_enumset1(X0,X1,X2,X3,X4,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_12,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 55.22/7.49      inference(cnf_transformation,[],[f72]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_457,plain,
% 55.22/7.49      ( k5_enumset1(X0,X0,X0,X0,X1,X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_6,plain,
% 55.22/7.49      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
% 55.22/7.49      inference(cnf_transformation,[],[f66]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_13,negated_conjecture,
% 55.22/7.49      ( k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 55.22/7.49      inference(cnf_transformation,[],[f73]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_392,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_6,c_13]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.22/7.49      inference(cnf_transformation,[],[f65]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_404,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1)))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_4,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 55.22/7.49      inference(cnf_transformation,[],[f34]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_5,plain,
% 55.22/7.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.22/7.49      inference(cnf_transformation,[],[f35]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_138,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_135,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_1,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 55.22/7.49      inference(cnf_transformation,[],[f64]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_38,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_1,c_5,c_12]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_142,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_135,c_38]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_247,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_138,c_142]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_3,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.22/7.49      inference(cnf_transformation,[],[f33]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_255,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_247,c_3]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_267,plain,
% 55.22/7.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_255,c_142]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_272,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_267]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_262,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_255]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_1962,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_272,c_262]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_271,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_267]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_265,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_255,c_255]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_575,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_265,c_4]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_3210,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_271,c_575]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_264,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_142,c_255]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_552,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_264,c_4]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2692,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_552,c_552]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_3328,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_3210,c_2692]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_15413,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1)),X0))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_404,c_1962,c_3328]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_15429,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k1_xboole_0,sK1))) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_392,c_15413]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_15440,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_15429,c_12,c_38]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_406,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))))) = k3_tarski(k5_enumset1(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2,c_2]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_1916,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_3,c_272]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2017,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_1916,c_264]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_149,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_142]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2212,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2017,c_149]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2237,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_2212,c_3]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2016,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_1916,c_265]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2094,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_2016]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_7465,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,X2)),k1_xboole_0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2237,c_2094]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_7584,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_7465,c_2094]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2020,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_1916,c_271]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_152,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_142,c_4]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_154,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_152,c_4]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_804,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_154,c_265]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_15119,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,X2)),X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2020,c_804]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2168,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_2017]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_855,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_262,c_262]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9769,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X1,X2)),X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2168,c_855]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2202,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_272,c_2017]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2241,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_2202,c_4]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9771,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X3)),X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2241,c_855]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9499,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2241,c_552]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_836,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_142,c_262]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9533,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X3)),X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2241,c_836]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2189,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_2017]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_8843,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X0))) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_2189,c_575]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_1990,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_1916]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_5295,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X1)),X0) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_1990,c_804]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_273,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_267]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_4767,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X3)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_273,c_1990]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_4771,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_1990]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_4836,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_1990,c_4]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2356,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_273,c_1916]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2382,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_273,c_1916]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2404,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_2382,c_2020]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2424,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_2356,c_2404]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_4870,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X2,X0),k5_xboole_0(X1,X3)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_4836,c_1916,c_2424,c_3328]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_4935,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_4767,c_4771,c_4870]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_5411,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X2,X1))) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_5295,c_4935]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_8874,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X2,X0))) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_8843,c_5411]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9544,plain,
% 55.22/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_9533,c_8874]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9577,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X0,X3))) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_9499,c_9544]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9980,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_9771,c_9577]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_9981,plain,
% 55.22/7.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X0,X2))) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_9769,c_9980]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_15187,plain,
% 55.22/7.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X3,X2))) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_15119,c_9981]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_17935,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),X1)) ),
% 55.22/7.49      inference(demodulation,
% 55.22/7.49                [status(thm)],
% 55.22/7.49                [c_406,c_1962,c_3328,c_7584,c_15187]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_17936,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1)))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),k5_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1),X1)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_17935,c_1962,c_3328]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_18140,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(sK1,k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_15440,c_17936]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_18233,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_18140,c_255]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_20450,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) = k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k5_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_6,c_18233]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_20468,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) = k3_tarski(k5_enumset1(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0)) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_20450,c_392]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_402,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X0)))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_12,c_2]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_407,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_402,c_5,c_12,c_38]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_20469,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),sK1)) = sK1 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_20468,c_38,c_407]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_20474,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1))) = sK1 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_6,c_20469]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_48153,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1),k5_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1))) = sK1 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_457,c_20474]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_395,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_413,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_395,c_142]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_27869,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_15440,c_413]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_48145,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_457,c_27869]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_400,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,X1))))))) = k3_tarski(k5_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),X0)) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_142,c_2]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_33253,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))))) = k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_27869,c_400]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_33272,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) = k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_6,c_33253]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_33290,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k1_xboole_0)))) = k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_33272,c_392]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_33291,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_33290,c_3,c_12]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_48162,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_457,c_33291]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_49729,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_6,c_48162]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_51077,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_457,c_49729]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_57094,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_48145,c_51077]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_57401,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1),k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1),k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK1))) = sK1 ),
% 55.22/7.49      inference(light_normalisation,
% 55.22/7.49                [status(thm)],
% 55.22/7.49                [c_48153,c_48153,c_57094]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_57402,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_57401,c_264]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_57403,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_1418,c_57402]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_48883,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_1418,c_392]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_57407,plain,
% 55.22/7.49      ( sK1 = k1_xboole_0 ),
% 55.22/7.49      inference(light_normalisation,[status(thm)],[c_57403,c_48883]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_57408,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_57407,c_57402]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_2446,plain,
% 55.22/7.49      ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0,X0,X0)) = X0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_6,c_407]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_63011,plain,
% 55.22/7.49      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 55.22/7.49      inference(superposition,[status(thm)],[c_57408,c_2446]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_11,plain,
% 55.22/7.49      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 55.22/7.49      inference(cnf_transformation,[],[f74]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_39,plain,
% 55.22/7.49      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 55.22/7.49      inference(demodulation,[status(thm)],[c_11,c_5,c_9,c_38]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(c_41,plain,
% 55.22/7.49      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
% 55.22/7.49      inference(instantiation,[status(thm)],[c_39]) ).
% 55.22/7.49  
% 55.22/7.49  cnf(contradiction,plain,
% 55.22/7.49      ( $false ),
% 55.22/7.49      inference(minisat,[status(thm)],[c_63011,c_41]) ).
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  % SZS output end CNFRefutation for theBenchmark.p
% 55.22/7.49  
% 55.22/7.49  ------                               Statistics
% 55.22/7.49  
% 55.22/7.49  ------ General
% 55.22/7.49  
% 55.22/7.49  abstr_ref_over_cycles:                  0
% 55.22/7.49  abstr_ref_under_cycles:                 0
% 55.22/7.49  gc_basic_clause_elim:                   0
% 55.22/7.49  forced_gc_time:                         0
% 55.22/7.49  parsing_time:                           0.009
% 55.22/7.49  unif_index_cands_time:                  0.
% 55.22/7.49  unif_index_add_time:                    0.
% 55.22/7.49  orderings_time:                         0.
% 55.22/7.49  out_proof_time:                         0.015
% 55.22/7.49  total_time:                             6.67
% 55.22/7.49  num_of_symbols:                         37
% 55.22/7.49  num_of_terms:                           133345
% 55.22/7.49  
% 55.22/7.49  ------ Preprocessing
% 55.22/7.49  
% 55.22/7.49  num_of_splits:                          0
% 55.22/7.49  num_of_split_atoms:                     0
% 55.22/7.49  num_of_reused_defs:                     0
% 55.22/7.49  num_eq_ax_congr_red:                    0
% 55.22/7.49  num_of_sem_filtered_clauses:            0
% 55.22/7.49  num_of_subtypes:                        0
% 55.22/7.49  monotx_restored_types:                  0
% 55.22/7.49  sat_num_of_epr_types:                   0
% 55.22/7.49  sat_num_of_non_cyclic_types:            0
% 55.22/7.49  sat_guarded_non_collapsed_types:        0
% 55.22/7.49  num_pure_diseq_elim:                    0
% 55.22/7.49  simp_replaced_by:                       0
% 55.22/7.49  res_preprocessed:                       33
% 55.22/7.49  prep_upred:                             0
% 55.22/7.49  prep_unflattend:                        0
% 55.22/7.49  smt_new_axioms:                         0
% 55.22/7.49  pred_elim_cands:                        0
% 55.22/7.49  pred_elim:                              0
% 55.22/7.49  pred_elim_cl:                           0
% 55.22/7.49  pred_elim_cycles:                       0
% 55.22/7.49  merged_defs:                            0
% 55.22/7.49  merged_defs_ncl:                        0
% 55.22/7.49  bin_hyper_res:                          0
% 55.22/7.49  prep_cycles:                            2
% 55.22/7.49  pred_elim_time:                         0.
% 55.22/7.49  splitting_time:                         0.
% 55.22/7.49  sem_filter_time:                        0.
% 55.22/7.49  monotx_time:                            0.001
% 55.22/7.49  subtype_inf_time:                       0.
% 55.22/7.49  
% 55.22/7.49  ------ Problem properties
% 55.22/7.49  
% 55.22/7.49  clauses:                                14
% 55.22/7.49  conjectures:                            1
% 55.22/7.49  epr:                                    0
% 55.22/7.49  horn:                                   13
% 55.22/7.49  ground:                                 1
% 55.22/7.49  unary:                                  13
% 55.22/7.49  binary:                                 1
% 55.22/7.49  lits:                                   15
% 55.22/7.49  lits_eq:                                15
% 55.22/7.49  fd_pure:                                0
% 55.22/7.49  fd_pseudo:                              0
% 55.22/7.49  fd_cond:                                0
% 55.22/7.49  fd_pseudo_cond:                         1
% 55.22/7.49  ac_symbols:                             1
% 55.22/7.49  
% 55.22/7.49  ------ Propositional Solver
% 55.22/7.49  
% 55.22/7.49  prop_solver_calls:                      26
% 55.22/7.49  prop_fast_solver_calls:                 300
% 55.22/7.49  smt_solver_calls:                       0
% 55.22/7.49  smt_fast_solver_calls:                  0
% 55.22/7.49  prop_num_of_clauses:                    6003
% 55.22/7.49  prop_preprocess_simplified:             16168
% 55.22/7.49  prop_fo_subsumed:                       0
% 55.22/7.49  prop_solver_time:                       0.
% 55.22/7.49  smt_solver_time:                        0.
% 55.22/7.49  smt_fast_solver_time:                   0.
% 55.22/7.49  prop_fast_solver_time:                  0.
% 55.22/7.49  prop_unsat_core_time:                   0.
% 55.22/7.49  
% 55.22/7.49  ------ QBF
% 55.22/7.49  
% 55.22/7.49  qbf_q_res:                              0
% 55.22/7.49  qbf_num_tautologies:                    0
% 55.22/7.49  qbf_prep_cycles:                        0
% 55.22/7.49  
% 55.22/7.49  ------ BMC1
% 55.22/7.49  
% 55.22/7.49  bmc1_current_bound:                     -1
% 55.22/7.49  bmc1_last_solved_bound:                 -1
% 55.22/7.49  bmc1_unsat_core_size:                   -1
% 55.22/7.49  bmc1_unsat_core_parents_size:           -1
% 55.22/7.49  bmc1_merge_next_fun:                    0
% 55.22/7.49  bmc1_unsat_core_clauses_time:           0.
% 55.22/7.49  
% 55.22/7.49  ------ Instantiation
% 55.22/7.49  
% 55.22/7.49  inst_num_of_clauses:                    3235
% 55.22/7.49  inst_num_in_passive:                    1999
% 55.22/7.49  inst_num_in_active:                     542
% 55.22/7.49  inst_num_in_unprocessed:                694
% 55.22/7.49  inst_num_of_loops:                      780
% 55.22/7.49  inst_num_of_learning_restarts:          0
% 55.22/7.49  inst_num_moves_active_passive:          233
% 55.22/7.49  inst_lit_activity:                      0
% 55.22/7.49  inst_lit_activity_moves:                0
% 55.22/7.49  inst_num_tautologies:                   0
% 55.22/7.49  inst_num_prop_implied:                  0
% 55.22/7.49  inst_num_existing_simplified:           0
% 55.22/7.49  inst_num_eq_res_simplified:             0
% 55.22/7.49  inst_num_child_elim:                    0
% 55.22/7.49  inst_num_of_dismatching_blockings:      7282
% 55.22/7.49  inst_num_of_non_proper_insts:           4053
% 55.22/7.49  inst_num_of_duplicates:                 0
% 55.22/7.49  inst_inst_num_from_inst_to_res:         0
% 55.22/7.49  inst_dismatching_checking_time:         0.
% 55.22/7.49  
% 55.22/7.49  ------ Resolution
% 55.22/7.49  
% 55.22/7.49  res_num_of_clauses:                     0
% 55.22/7.49  res_num_in_passive:                     0
% 55.22/7.49  res_num_in_active:                      0
% 55.22/7.49  res_num_of_loops:                       35
% 55.22/7.49  res_forward_subset_subsumed:            210
% 55.22/7.49  res_backward_subset_subsumed:           2
% 55.22/7.49  res_forward_subsumed:                   0
% 55.22/7.49  res_backward_subsumed:                  0
% 55.22/7.49  res_forward_subsumption_resolution:     0
% 55.22/7.49  res_backward_subsumption_resolution:    0
% 55.22/7.49  res_clause_to_clause_subsumption:       81041
% 55.22/7.49  res_orphan_elimination:                 0
% 55.22/7.49  res_tautology_del:                      391
% 55.22/7.49  res_num_eq_res_simplified:              0
% 55.22/7.49  res_num_sel_changes:                    0
% 55.22/7.49  res_moves_from_active_to_pass:          0
% 55.22/7.49  
% 55.22/7.49  ------ Superposition
% 55.22/7.49  
% 55.22/7.49  sup_time_total:                         0.
% 55.22/7.49  sup_time_generating:                    0.
% 55.22/7.49  sup_time_sim_full:                      0.
% 55.22/7.49  sup_time_sim_immed:                     0.
% 55.22/7.49  
% 55.22/7.49  sup_num_of_clauses:                     1716
% 55.22/7.49  sup_num_in_active:                      98
% 55.22/7.49  sup_num_in_passive:                     1618
% 55.22/7.49  sup_num_of_loops:                       155
% 55.22/7.49  sup_fw_superposition:                   14005
% 55.22/7.49  sup_bw_superposition:                   7990
% 55.22/7.49  sup_immediate_simplified:               11781
% 55.22/7.49  sup_given_eliminated:                   12
% 55.22/7.49  comparisons_done:                       0
% 55.22/7.49  comparisons_avoided:                    1
% 55.22/7.49  
% 55.22/7.49  ------ Simplifications
% 55.22/7.49  
% 55.22/7.49  
% 55.22/7.49  sim_fw_subset_subsumed:                 0
% 55.22/7.49  sim_bw_subset_subsumed:                 0
% 55.22/7.49  sim_fw_subsumed:                        267
% 55.22/7.49  sim_bw_subsumed:                        4
% 55.22/7.49  sim_fw_subsumption_res:                 0
% 55.22/7.49  sim_bw_subsumption_res:                 0
% 55.22/7.49  sim_tautology_del:                      0
% 55.22/7.49  sim_eq_tautology_del:                   2359
% 55.22/7.49  sim_eq_res_simp:                        0
% 55.22/7.49  sim_fw_demodulated:                     13975
% 55.22/7.49  sim_bw_demodulated:                     93
% 55.22/7.49  sim_light_normalised:                   2633
% 55.22/7.49  sim_joinable_taut:                      538
% 55.22/7.49  sim_joinable_simp:                      0
% 55.22/7.49  sim_ac_normalised:                      0
% 55.22/7.49  sim_smt_subsumption:                    0
% 55.22/7.49  
%------------------------------------------------------------------------------
