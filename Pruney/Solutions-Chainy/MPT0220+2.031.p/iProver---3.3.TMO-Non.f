%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:32 EST 2020

% Result     : Timeout 59.36s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  100 ( 303 expanded)
%              Number of clauses        :   42 (  80 expanded)
%              Number of leaves         :   21 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :  106 ( 314 expanded)
%              Number of equality atoms :   93 ( 297 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f53,f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f25,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f46,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f58,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f46,f47,f53,f52,f52])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f33,f30,f30,f47])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_136,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_138,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1939,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_136,c_138])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_218,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_10])).

cnf(c_195419,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1939,c_218])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_137,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_569,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_137])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_262,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_578,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_569,c_262])).

cnf(c_1941,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_578,c_138])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_143,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_795,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_143])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_70,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_8,c_1])).

cnf(c_831,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0),X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_795,c_70])).

cnf(c_142,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_836,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_795,c_142])).

cnf(c_837,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))),k1_xboole_0),k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_795,c_70])).

cnf(c_851,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))),k1_xboole_0),k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_837,c_4])).

cnf(c_337,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_725,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_337,c_142])).

cnf(c_852,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_851,c_725])).

cnf(c_853,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_852,c_262])).

cnf(c_857,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_831,c_836,c_853])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_858,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_857,c_2,c_4])).

cnf(c_859,plain,
    ( k5_xboole_0(X0,X0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_858,c_262])).

cnf(c_2318,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1941,c_859])).

cnf(c_144,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_2449,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2318,c_144])).

cnf(c_2454,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2449,c_6])).

cnf(c_195420,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_195419,c_2454])).

cnf(c_195421,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_195420])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.36/8.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.36/8.01  
% 59.36/8.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.36/8.01  
% 59.36/8.01  ------  iProver source info
% 59.36/8.01  
% 59.36/8.01  git: date: 2020-06-30 10:37:57 +0100
% 59.36/8.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.36/8.01  git: non_committed_changes: false
% 59.36/8.01  git: last_make_outside_of_git: false
% 59.36/8.01  
% 59.36/8.01  ------ 
% 59.36/8.01  
% 59.36/8.01  ------ Input Options
% 59.36/8.01  
% 59.36/8.01  --out_options                           all
% 59.36/8.01  --tptp_safe_out                         true
% 59.36/8.01  --problem_path                          ""
% 59.36/8.01  --include_path                          ""
% 59.36/8.01  --clausifier                            res/vclausify_rel
% 59.36/8.01  --clausifier_options                    ""
% 59.36/8.01  --stdin                                 false
% 59.36/8.01  --stats_out                             all
% 59.36/8.01  
% 59.36/8.01  ------ General Options
% 59.36/8.01  
% 59.36/8.01  --fof                                   false
% 59.36/8.01  --time_out_real                         305.
% 59.36/8.01  --time_out_virtual                      -1.
% 59.36/8.01  --symbol_type_check                     false
% 59.36/8.01  --clausify_out                          false
% 59.36/8.01  --sig_cnt_out                           false
% 59.36/8.01  --trig_cnt_out                          false
% 59.36/8.01  --trig_cnt_out_tolerance                1.
% 59.36/8.01  --trig_cnt_out_sk_spl                   false
% 59.36/8.01  --abstr_cl_out                          false
% 59.36/8.01  
% 59.36/8.01  ------ Global Options
% 59.36/8.01  
% 59.36/8.01  --schedule                              default
% 59.36/8.01  --add_important_lit                     false
% 59.36/8.01  --prop_solver_per_cl                    1000
% 59.36/8.01  --min_unsat_core                        false
% 59.36/8.01  --soft_assumptions                      false
% 59.36/8.01  --soft_lemma_size                       3
% 59.36/8.01  --prop_impl_unit_size                   0
% 59.36/8.01  --prop_impl_unit                        []
% 59.36/8.01  --share_sel_clauses                     true
% 59.36/8.01  --reset_solvers                         false
% 59.36/8.01  --bc_imp_inh                            [conj_cone]
% 59.36/8.01  --conj_cone_tolerance                   3.
% 59.36/8.01  --extra_neg_conj                        none
% 59.36/8.01  --large_theory_mode                     true
% 59.36/8.01  --prolific_symb_bound                   200
% 59.36/8.01  --lt_threshold                          2000
% 59.36/8.01  --clause_weak_htbl                      true
% 59.36/8.01  --gc_record_bc_elim                     false
% 59.36/8.01  
% 59.36/8.01  ------ Preprocessing Options
% 59.36/8.01  
% 59.36/8.01  --preprocessing_flag                    true
% 59.36/8.01  --time_out_prep_mult                    0.1
% 59.36/8.01  --splitting_mode                        input
% 59.36/8.01  --splitting_grd                         true
% 59.36/8.01  --splitting_cvd                         false
% 59.36/8.01  --splitting_cvd_svl                     false
% 59.36/8.01  --splitting_nvd                         32
% 59.36/8.01  --sub_typing                            true
% 59.36/8.01  --prep_gs_sim                           true
% 59.36/8.01  --prep_unflatten                        true
% 59.36/8.01  --prep_res_sim                          true
% 59.36/8.01  --prep_upred                            true
% 59.36/8.01  --prep_sem_filter                       exhaustive
% 59.36/8.01  --prep_sem_filter_out                   false
% 59.36/8.01  --pred_elim                             true
% 59.36/8.01  --res_sim_input                         true
% 59.36/8.01  --eq_ax_congr_red                       true
% 59.36/8.01  --pure_diseq_elim                       true
% 59.36/8.01  --brand_transform                       false
% 59.36/8.01  --non_eq_to_eq                          false
% 59.36/8.01  --prep_def_merge                        true
% 59.36/8.01  --prep_def_merge_prop_impl              false
% 59.36/8.01  --prep_def_merge_mbd                    true
% 59.36/8.01  --prep_def_merge_tr_red                 false
% 59.36/8.01  --prep_def_merge_tr_cl                  false
% 59.36/8.01  --smt_preprocessing                     true
% 59.36/8.01  --smt_ac_axioms                         fast
% 59.36/8.01  --preprocessed_out                      false
% 59.36/8.01  --preprocessed_stats                    false
% 59.36/8.01  
% 59.36/8.01  ------ Abstraction refinement Options
% 59.36/8.01  
% 59.36/8.01  --abstr_ref                             []
% 59.36/8.01  --abstr_ref_prep                        false
% 59.36/8.01  --abstr_ref_until_sat                   false
% 59.36/8.01  --abstr_ref_sig_restrict                funpre
% 59.36/8.01  --abstr_ref_af_restrict_to_split_sk     false
% 59.36/8.01  --abstr_ref_under                       []
% 59.36/8.01  
% 59.36/8.01  ------ SAT Options
% 59.36/8.01  
% 59.36/8.01  --sat_mode                              false
% 59.36/8.01  --sat_fm_restart_options                ""
% 59.36/8.01  --sat_gr_def                            false
% 59.36/8.01  --sat_epr_types                         true
% 59.36/8.01  --sat_non_cyclic_types                  false
% 59.36/8.01  --sat_finite_models                     false
% 59.36/8.01  --sat_fm_lemmas                         false
% 59.36/8.01  --sat_fm_prep                           false
% 59.36/8.01  --sat_fm_uc_incr                        true
% 59.36/8.01  --sat_out_model                         small
% 59.36/8.01  --sat_out_clauses                       false
% 59.36/8.01  
% 59.36/8.01  ------ QBF Options
% 59.36/8.01  
% 59.36/8.01  --qbf_mode                              false
% 59.36/8.01  --qbf_elim_univ                         false
% 59.36/8.01  --qbf_dom_inst                          none
% 59.36/8.01  --qbf_dom_pre_inst                      false
% 59.36/8.01  --qbf_sk_in                             false
% 59.36/8.01  --qbf_pred_elim                         true
% 59.36/8.01  --qbf_split                             512
% 59.36/8.01  
% 59.36/8.01  ------ BMC1 Options
% 59.36/8.01  
% 59.36/8.01  --bmc1_incremental                      false
% 59.36/8.01  --bmc1_axioms                           reachable_all
% 59.36/8.01  --bmc1_min_bound                        0
% 59.36/8.01  --bmc1_max_bound                        -1
% 59.36/8.01  --bmc1_max_bound_default                -1
% 59.36/8.01  --bmc1_symbol_reachability              true
% 59.36/8.01  --bmc1_property_lemmas                  false
% 59.36/8.01  --bmc1_k_induction                      false
% 59.36/8.01  --bmc1_non_equiv_states                 false
% 59.36/8.01  --bmc1_deadlock                         false
% 59.36/8.01  --bmc1_ucm                              false
% 59.36/8.01  --bmc1_add_unsat_core                   none
% 59.36/8.01  --bmc1_unsat_core_children              false
% 59.36/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.36/8.01  --bmc1_out_stat                         full
% 59.36/8.01  --bmc1_ground_init                      false
% 59.36/8.01  --bmc1_pre_inst_next_state              false
% 59.36/8.01  --bmc1_pre_inst_state                   false
% 59.36/8.01  --bmc1_pre_inst_reach_state             false
% 59.36/8.01  --bmc1_out_unsat_core                   false
% 59.36/8.01  --bmc1_aig_witness_out                  false
% 59.36/8.01  --bmc1_verbose                          false
% 59.36/8.01  --bmc1_dump_clauses_tptp                false
% 59.36/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.36/8.01  --bmc1_dump_file                        -
% 59.36/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.36/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.36/8.01  --bmc1_ucm_extend_mode                  1
% 59.36/8.01  --bmc1_ucm_init_mode                    2
% 59.36/8.01  --bmc1_ucm_cone_mode                    none
% 59.36/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.36/8.01  --bmc1_ucm_relax_model                  4
% 59.36/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.36/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.36/8.01  --bmc1_ucm_layered_model                none
% 59.36/8.01  --bmc1_ucm_max_lemma_size               10
% 59.36/8.01  
% 59.36/8.01  ------ AIG Options
% 59.36/8.01  
% 59.36/8.01  --aig_mode                              false
% 59.36/8.01  
% 59.36/8.01  ------ Instantiation Options
% 59.36/8.01  
% 59.36/8.01  --instantiation_flag                    true
% 59.36/8.01  --inst_sos_flag                         true
% 59.36/8.01  --inst_sos_phase                        true
% 59.36/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.36/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.36/8.01  --inst_lit_sel_side                     num_symb
% 59.36/8.01  --inst_solver_per_active                1400
% 59.36/8.01  --inst_solver_calls_frac                1.
% 59.36/8.01  --inst_passive_queue_type               priority_queues
% 59.36/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.36/8.01  --inst_passive_queues_freq              [25;2]
% 59.36/8.01  --inst_dismatching                      true
% 59.36/8.01  --inst_eager_unprocessed_to_passive     true
% 59.36/8.01  --inst_prop_sim_given                   true
% 59.36/8.01  --inst_prop_sim_new                     false
% 59.36/8.01  --inst_subs_new                         false
% 59.36/8.01  --inst_eq_res_simp                      false
% 59.36/8.01  --inst_subs_given                       false
% 59.36/8.01  --inst_orphan_elimination               true
% 59.36/8.01  --inst_learning_loop_flag               true
% 59.36/8.01  --inst_learning_start                   3000
% 59.36/8.01  --inst_learning_factor                  2
% 59.36/8.01  --inst_start_prop_sim_after_learn       3
% 59.36/8.01  --inst_sel_renew                        solver
% 59.36/8.01  --inst_lit_activity_flag                true
% 59.36/8.01  --inst_restr_to_given                   false
% 59.36/8.01  --inst_activity_threshold               500
% 59.36/8.01  --inst_out_proof                        true
% 59.36/8.01  
% 59.36/8.01  ------ Resolution Options
% 59.36/8.01  
% 59.36/8.01  --resolution_flag                       true
% 59.36/8.01  --res_lit_sel                           adaptive
% 59.36/8.01  --res_lit_sel_side                      none
% 59.36/8.01  --res_ordering                          kbo
% 59.36/8.01  --res_to_prop_solver                    active
% 59.36/8.01  --res_prop_simpl_new                    false
% 59.36/8.01  --res_prop_simpl_given                  true
% 59.36/8.01  --res_passive_queue_type                priority_queues
% 59.36/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.36/8.01  --res_passive_queues_freq               [15;5]
% 59.36/8.01  --res_forward_subs                      full
% 59.36/8.01  --res_backward_subs                     full
% 59.36/8.01  --res_forward_subs_resolution           true
% 59.36/8.01  --res_backward_subs_resolution          true
% 59.36/8.01  --res_orphan_elimination                true
% 59.36/8.01  --res_time_limit                        2.
% 59.36/8.01  --res_out_proof                         true
% 59.36/8.01  
% 59.36/8.01  ------ Superposition Options
% 59.36/8.01  
% 59.36/8.01  --superposition_flag                    true
% 59.36/8.01  --sup_passive_queue_type                priority_queues
% 59.36/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.36/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.36/8.01  --demod_completeness_check              fast
% 59.36/8.01  --demod_use_ground                      true
% 59.36/8.01  --sup_to_prop_solver                    passive
% 59.36/8.01  --sup_prop_simpl_new                    true
% 59.36/8.01  --sup_prop_simpl_given                  true
% 59.36/8.01  --sup_fun_splitting                     true
% 59.36/8.01  --sup_smt_interval                      50000
% 59.36/8.01  
% 59.36/8.01  ------ Superposition Simplification Setup
% 59.36/8.01  
% 59.36/8.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.36/8.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.36/8.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.36/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.36/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.36/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.36/8.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.36/8.01  --sup_immed_triv                        [TrivRules]
% 59.36/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.36/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.36/8.01  --sup_immed_bw_main                     []
% 59.36/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.36/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.36/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.36/8.01  --sup_input_bw                          []
% 59.36/8.01  
% 59.36/8.01  ------ Combination Options
% 59.36/8.01  
% 59.36/8.01  --comb_res_mult                         3
% 59.36/8.01  --comb_sup_mult                         2
% 59.36/8.01  --comb_inst_mult                        10
% 59.36/8.01  
% 59.36/8.01  ------ Debug Options
% 59.36/8.01  
% 59.36/8.01  --dbg_backtrace                         false
% 59.36/8.01  --dbg_dump_prop_clauses                 false
% 59.36/8.01  --dbg_dump_prop_clauses_file            -
% 59.36/8.01  --dbg_out_stat                          false
% 59.36/8.01  ------ Parsing...
% 59.36/8.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.36/8.01  
% 59.36/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.36/8.01  
% 59.36/8.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.36/8.01  
% 59.36/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.36/8.01  ------ Proving...
% 59.36/8.01  ------ Problem Properties 
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  clauses                                 11
% 59.36/8.01  conjectures                             1
% 59.36/8.01  EPR                                     0
% 59.36/8.01  Horn                                    11
% 59.36/8.01  unary                                   10
% 59.36/8.01  binary                                  1
% 59.36/8.01  lits                                    12
% 59.36/8.01  lits eq                                 9
% 59.36/8.01  fd_pure                                 0
% 59.36/8.01  fd_pseudo                               0
% 59.36/8.01  fd_cond                                 0
% 59.36/8.01  fd_pseudo_cond                          0
% 59.36/8.01  AC symbols                              1
% 59.36/8.01  
% 59.36/8.01  ------ Schedule dynamic 5 is on 
% 59.36/8.01  
% 59.36/8.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  ------ 
% 59.36/8.01  Current options:
% 59.36/8.01  ------ 
% 59.36/8.01  
% 59.36/8.01  ------ Input Options
% 59.36/8.01  
% 59.36/8.01  --out_options                           all
% 59.36/8.01  --tptp_safe_out                         true
% 59.36/8.01  --problem_path                          ""
% 59.36/8.01  --include_path                          ""
% 59.36/8.01  --clausifier                            res/vclausify_rel
% 59.36/8.01  --clausifier_options                    ""
% 59.36/8.01  --stdin                                 false
% 59.36/8.01  --stats_out                             all
% 59.36/8.01  
% 59.36/8.01  ------ General Options
% 59.36/8.01  
% 59.36/8.01  --fof                                   false
% 59.36/8.01  --time_out_real                         305.
% 59.36/8.01  --time_out_virtual                      -1.
% 59.36/8.01  --symbol_type_check                     false
% 59.36/8.01  --clausify_out                          false
% 59.36/8.01  --sig_cnt_out                           false
% 59.36/8.01  --trig_cnt_out                          false
% 59.36/8.01  --trig_cnt_out_tolerance                1.
% 59.36/8.01  --trig_cnt_out_sk_spl                   false
% 59.36/8.01  --abstr_cl_out                          false
% 59.36/8.01  
% 59.36/8.01  ------ Global Options
% 59.36/8.01  
% 59.36/8.01  --schedule                              default
% 59.36/8.01  --add_important_lit                     false
% 59.36/8.01  --prop_solver_per_cl                    1000
% 59.36/8.01  --min_unsat_core                        false
% 59.36/8.01  --soft_assumptions                      false
% 59.36/8.01  --soft_lemma_size                       3
% 59.36/8.01  --prop_impl_unit_size                   0
% 59.36/8.01  --prop_impl_unit                        []
% 59.36/8.01  --share_sel_clauses                     true
% 59.36/8.01  --reset_solvers                         false
% 59.36/8.01  --bc_imp_inh                            [conj_cone]
% 59.36/8.01  --conj_cone_tolerance                   3.
% 59.36/8.01  --extra_neg_conj                        none
% 59.36/8.01  --large_theory_mode                     true
% 59.36/8.01  --prolific_symb_bound                   200
% 59.36/8.01  --lt_threshold                          2000
% 59.36/8.01  --clause_weak_htbl                      true
% 59.36/8.01  --gc_record_bc_elim                     false
% 59.36/8.01  
% 59.36/8.01  ------ Preprocessing Options
% 59.36/8.01  
% 59.36/8.01  --preprocessing_flag                    true
% 59.36/8.01  --time_out_prep_mult                    0.1
% 59.36/8.01  --splitting_mode                        input
% 59.36/8.01  --splitting_grd                         true
% 59.36/8.01  --splitting_cvd                         false
% 59.36/8.01  --splitting_cvd_svl                     false
% 59.36/8.01  --splitting_nvd                         32
% 59.36/8.01  --sub_typing                            true
% 59.36/8.01  --prep_gs_sim                           true
% 59.36/8.01  --prep_unflatten                        true
% 59.36/8.01  --prep_res_sim                          true
% 59.36/8.01  --prep_upred                            true
% 59.36/8.01  --prep_sem_filter                       exhaustive
% 59.36/8.01  --prep_sem_filter_out                   false
% 59.36/8.01  --pred_elim                             true
% 59.36/8.01  --res_sim_input                         true
% 59.36/8.01  --eq_ax_congr_red                       true
% 59.36/8.01  --pure_diseq_elim                       true
% 59.36/8.01  --brand_transform                       false
% 59.36/8.01  --non_eq_to_eq                          false
% 59.36/8.01  --prep_def_merge                        true
% 59.36/8.01  --prep_def_merge_prop_impl              false
% 59.36/8.01  --prep_def_merge_mbd                    true
% 59.36/8.01  --prep_def_merge_tr_red                 false
% 59.36/8.01  --prep_def_merge_tr_cl                  false
% 59.36/8.01  --smt_preprocessing                     true
% 59.36/8.01  --smt_ac_axioms                         fast
% 59.36/8.01  --preprocessed_out                      false
% 59.36/8.01  --preprocessed_stats                    false
% 59.36/8.01  
% 59.36/8.01  ------ Abstraction refinement Options
% 59.36/8.01  
% 59.36/8.01  --abstr_ref                             []
% 59.36/8.01  --abstr_ref_prep                        false
% 59.36/8.01  --abstr_ref_until_sat                   false
% 59.36/8.01  --abstr_ref_sig_restrict                funpre
% 59.36/8.01  --abstr_ref_af_restrict_to_split_sk     false
% 59.36/8.01  --abstr_ref_under                       []
% 59.36/8.01  
% 59.36/8.01  ------ SAT Options
% 59.36/8.01  
% 59.36/8.01  --sat_mode                              false
% 59.36/8.01  --sat_fm_restart_options                ""
% 59.36/8.01  --sat_gr_def                            false
% 59.36/8.01  --sat_epr_types                         true
% 59.36/8.01  --sat_non_cyclic_types                  false
% 59.36/8.01  --sat_finite_models                     false
% 59.36/8.01  --sat_fm_lemmas                         false
% 59.36/8.01  --sat_fm_prep                           false
% 59.36/8.01  --sat_fm_uc_incr                        true
% 59.36/8.01  --sat_out_model                         small
% 59.36/8.01  --sat_out_clauses                       false
% 59.36/8.01  
% 59.36/8.01  ------ QBF Options
% 59.36/8.01  
% 59.36/8.01  --qbf_mode                              false
% 59.36/8.01  --qbf_elim_univ                         false
% 59.36/8.01  --qbf_dom_inst                          none
% 59.36/8.01  --qbf_dom_pre_inst                      false
% 59.36/8.01  --qbf_sk_in                             false
% 59.36/8.01  --qbf_pred_elim                         true
% 59.36/8.01  --qbf_split                             512
% 59.36/8.01  
% 59.36/8.01  ------ BMC1 Options
% 59.36/8.01  
% 59.36/8.01  --bmc1_incremental                      false
% 59.36/8.01  --bmc1_axioms                           reachable_all
% 59.36/8.01  --bmc1_min_bound                        0
% 59.36/8.01  --bmc1_max_bound                        -1
% 59.36/8.01  --bmc1_max_bound_default                -1
% 59.36/8.01  --bmc1_symbol_reachability              true
% 59.36/8.01  --bmc1_property_lemmas                  false
% 59.36/8.01  --bmc1_k_induction                      false
% 59.36/8.01  --bmc1_non_equiv_states                 false
% 59.36/8.01  --bmc1_deadlock                         false
% 59.36/8.01  --bmc1_ucm                              false
% 59.36/8.01  --bmc1_add_unsat_core                   none
% 59.36/8.01  --bmc1_unsat_core_children              false
% 59.36/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.36/8.01  --bmc1_out_stat                         full
% 59.36/8.01  --bmc1_ground_init                      false
% 59.36/8.01  --bmc1_pre_inst_next_state              false
% 59.36/8.01  --bmc1_pre_inst_state                   false
% 59.36/8.01  --bmc1_pre_inst_reach_state             false
% 59.36/8.01  --bmc1_out_unsat_core                   false
% 59.36/8.01  --bmc1_aig_witness_out                  false
% 59.36/8.01  --bmc1_verbose                          false
% 59.36/8.01  --bmc1_dump_clauses_tptp                false
% 59.36/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.36/8.01  --bmc1_dump_file                        -
% 59.36/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.36/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.36/8.01  --bmc1_ucm_extend_mode                  1
% 59.36/8.01  --bmc1_ucm_init_mode                    2
% 59.36/8.01  --bmc1_ucm_cone_mode                    none
% 59.36/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.36/8.01  --bmc1_ucm_relax_model                  4
% 59.36/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.36/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.36/8.01  --bmc1_ucm_layered_model                none
% 59.36/8.01  --bmc1_ucm_max_lemma_size               10
% 59.36/8.01  
% 59.36/8.01  ------ AIG Options
% 59.36/8.01  
% 59.36/8.01  --aig_mode                              false
% 59.36/8.01  
% 59.36/8.01  ------ Instantiation Options
% 59.36/8.01  
% 59.36/8.01  --instantiation_flag                    true
% 59.36/8.01  --inst_sos_flag                         true
% 59.36/8.01  --inst_sos_phase                        true
% 59.36/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.36/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.36/8.01  --inst_lit_sel_side                     none
% 59.36/8.01  --inst_solver_per_active                1400
% 59.36/8.01  --inst_solver_calls_frac                1.
% 59.36/8.01  --inst_passive_queue_type               priority_queues
% 59.36/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.36/8.01  --inst_passive_queues_freq              [25;2]
% 59.36/8.01  --inst_dismatching                      true
% 59.36/8.01  --inst_eager_unprocessed_to_passive     true
% 59.36/8.01  --inst_prop_sim_given                   true
% 59.36/8.01  --inst_prop_sim_new                     false
% 59.36/8.01  --inst_subs_new                         false
% 59.36/8.01  --inst_eq_res_simp                      false
% 59.36/8.01  --inst_subs_given                       false
% 59.36/8.01  --inst_orphan_elimination               true
% 59.36/8.01  --inst_learning_loop_flag               true
% 59.36/8.01  --inst_learning_start                   3000
% 59.36/8.01  --inst_learning_factor                  2
% 59.36/8.01  --inst_start_prop_sim_after_learn       3
% 59.36/8.01  --inst_sel_renew                        solver
% 59.36/8.01  --inst_lit_activity_flag                true
% 59.36/8.01  --inst_restr_to_given                   false
% 59.36/8.01  --inst_activity_threshold               500
% 59.36/8.01  --inst_out_proof                        true
% 59.36/8.01  
% 59.36/8.01  ------ Resolution Options
% 59.36/8.01  
% 59.36/8.01  --resolution_flag                       false
% 59.36/8.01  --res_lit_sel                           adaptive
% 59.36/8.01  --res_lit_sel_side                      none
% 59.36/8.01  --res_ordering                          kbo
% 59.36/8.01  --res_to_prop_solver                    active
% 59.36/8.01  --res_prop_simpl_new                    false
% 59.36/8.01  --res_prop_simpl_given                  true
% 59.36/8.01  --res_passive_queue_type                priority_queues
% 59.36/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.36/8.01  --res_passive_queues_freq               [15;5]
% 59.36/8.01  --res_forward_subs                      full
% 59.36/8.01  --res_backward_subs                     full
% 59.36/8.01  --res_forward_subs_resolution           true
% 59.36/8.01  --res_backward_subs_resolution          true
% 59.36/8.01  --res_orphan_elimination                true
% 59.36/8.01  --res_time_limit                        2.
% 59.36/8.01  --res_out_proof                         true
% 59.36/8.01  
% 59.36/8.01  ------ Superposition Options
% 59.36/8.01  
% 59.36/8.01  --superposition_flag                    true
% 59.36/8.01  --sup_passive_queue_type                priority_queues
% 59.36/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.36/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.36/8.01  --demod_completeness_check              fast
% 59.36/8.01  --demod_use_ground                      true
% 59.36/8.01  --sup_to_prop_solver                    passive
% 59.36/8.01  --sup_prop_simpl_new                    true
% 59.36/8.01  --sup_prop_simpl_given                  true
% 59.36/8.01  --sup_fun_splitting                     true
% 59.36/8.01  --sup_smt_interval                      50000
% 59.36/8.01  
% 59.36/8.01  ------ Superposition Simplification Setup
% 59.36/8.01  
% 59.36/8.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.36/8.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.36/8.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.36/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.36/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.36/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.36/8.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.36/8.01  --sup_immed_triv                        [TrivRules]
% 59.36/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.36/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.36/8.01  --sup_immed_bw_main                     []
% 59.36/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.36/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.36/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.36/8.01  --sup_input_bw                          []
% 59.36/8.01  
% 59.36/8.01  ------ Combination Options
% 59.36/8.01  
% 59.36/8.01  --comb_res_mult                         3
% 59.36/8.01  --comb_sup_mult                         2
% 59.36/8.01  --comb_inst_mult                        10
% 59.36/8.01  
% 59.36/8.01  ------ Debug Options
% 59.36/8.01  
% 59.36/8.01  --dbg_backtrace                         false
% 59.36/8.01  --dbg_dump_prop_clauses                 false
% 59.36/8.01  --dbg_dump_prop_clauses_file            -
% 59.36/8.01  --dbg_out_stat                          false
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  ------ Proving...
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  % SZS status Theorem for theBenchmark.p
% 59.36/8.01  
% 59.36/8.01   Resolution empty clause
% 59.36/8.01  
% 59.36/8.01  % SZS output start CNFRefutation for theBenchmark.p
% 59.36/8.01  
% 59.36/8.01  fof(f19,axiom,(
% 59.36/8.01    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f45,plain,(
% 59.36/8.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 59.36/8.01    inference(cnf_transformation,[],[f19])).
% 59.36/8.01  
% 59.36/8.01  fof(f12,axiom,(
% 59.36/8.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f38,plain,(
% 59.36/8.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f12])).
% 59.36/8.01  
% 59.36/8.01  fof(f53,plain,(
% 59.36/8.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 59.36/8.01    inference(definition_unfolding,[],[f38,f52])).
% 59.36/8.01  
% 59.36/8.01  fof(f13,axiom,(
% 59.36/8.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f39,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f13])).
% 59.36/8.01  
% 59.36/8.01  fof(f14,axiom,(
% 59.36/8.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f40,plain,(
% 59.36/8.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f14])).
% 59.36/8.01  
% 59.36/8.01  fof(f15,axiom,(
% 59.36/8.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f41,plain,(
% 59.36/8.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f15])).
% 59.36/8.01  
% 59.36/8.01  fof(f16,axiom,(
% 59.36/8.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f42,plain,(
% 59.36/8.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f16])).
% 59.36/8.01  
% 59.36/8.01  fof(f17,axiom,(
% 59.36/8.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f43,plain,(
% 59.36/8.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f17])).
% 59.36/8.01  
% 59.36/8.01  fof(f18,axiom,(
% 59.36/8.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f44,plain,(
% 59.36/8.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f18])).
% 59.36/8.01  
% 59.36/8.01  fof(f48,plain,(
% 59.36/8.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 59.36/8.01    inference(definition_unfolding,[],[f43,f44])).
% 59.36/8.01  
% 59.36/8.01  fof(f49,plain,(
% 59.36/8.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 59.36/8.01    inference(definition_unfolding,[],[f42,f48])).
% 59.36/8.01  
% 59.36/8.01  fof(f50,plain,(
% 59.36/8.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 59.36/8.01    inference(definition_unfolding,[],[f41,f49])).
% 59.36/8.01  
% 59.36/8.01  fof(f51,plain,(
% 59.36/8.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 59.36/8.01    inference(definition_unfolding,[],[f40,f50])).
% 59.36/8.01  
% 59.36/8.01  fof(f52,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 59.36/8.01    inference(definition_unfolding,[],[f39,f51])).
% 59.36/8.01  
% 59.36/8.01  fof(f57,plain,(
% 59.36/8.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 59.36/8.01    inference(definition_unfolding,[],[f45,f53,f52])).
% 59.36/8.01  
% 59.36/8.01  fof(f5,axiom,(
% 59.36/8.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f23,plain,(
% 59.36/8.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 59.36/8.01    inference(ennf_transformation,[],[f5])).
% 59.36/8.01  
% 59.36/8.01  fof(f31,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f23])).
% 59.36/8.01  
% 59.36/8.01  fof(f1,axiom,(
% 59.36/8.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f27,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f1])).
% 59.36/8.01  
% 59.36/8.01  fof(f20,conjecture,(
% 59.36/8.01    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f21,negated_conjecture,(
% 59.36/8.01    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 59.36/8.01    inference(negated_conjecture,[],[f20])).
% 59.36/8.01  
% 59.36/8.01  fof(f24,plain,(
% 59.36/8.01    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 59.36/8.01    inference(ennf_transformation,[],[f21])).
% 59.36/8.01  
% 59.36/8.01  fof(f25,plain,(
% 59.36/8.01    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 59.36/8.01    introduced(choice_axiom,[])).
% 59.36/8.01  
% 59.36/8.01  fof(f26,plain,(
% 59.36/8.01    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 59.36/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 59.36/8.01  
% 59.36/8.01  fof(f46,plain,(
% 59.36/8.01    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 59.36/8.01    inference(cnf_transformation,[],[f26])).
% 59.36/8.01  
% 59.36/8.01  fof(f11,axiom,(
% 59.36/8.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f37,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f11])).
% 59.36/8.01  
% 59.36/8.01  fof(f4,axiom,(
% 59.36/8.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f30,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f4])).
% 59.36/8.01  
% 59.36/8.01  fof(f47,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 59.36/8.01    inference(definition_unfolding,[],[f37,f30])).
% 59.36/8.01  
% 59.36/8.01  fof(f58,plain,(
% 59.36/8.01    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 59.36/8.01    inference(definition_unfolding,[],[f46,f47,f53,f52,f52])).
% 59.36/8.01  
% 59.36/8.01  fof(f6,axiom,(
% 59.36/8.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f32,plain,(
% 59.36/8.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.36/8.01    inference(cnf_transformation,[],[f6])).
% 59.36/8.01  
% 59.36/8.01  fof(f54,plain,(
% 59.36/8.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 59.36/8.01    inference(definition_unfolding,[],[f32,f30])).
% 59.36/8.01  
% 59.36/8.01  fof(f9,axiom,(
% 59.36/8.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f35,plain,(
% 59.36/8.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 59.36/8.01    inference(cnf_transformation,[],[f9])).
% 59.36/8.01  
% 59.36/8.01  fof(f56,plain,(
% 59.36/8.01    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 59.36/8.01    inference(definition_unfolding,[],[f35,f47])).
% 59.36/8.01  
% 59.36/8.01  fof(f8,axiom,(
% 59.36/8.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f34,plain,(
% 59.36/8.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.36/8.01    inference(cnf_transformation,[],[f8])).
% 59.36/8.01  
% 59.36/8.01  fof(f2,axiom,(
% 59.36/8.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f28,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f2])).
% 59.36/8.01  
% 59.36/8.01  fof(f10,axiom,(
% 59.36/8.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f36,plain,(
% 59.36/8.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f10])).
% 59.36/8.01  
% 59.36/8.01  fof(f7,axiom,(
% 59.36/8.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f33,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 59.36/8.01    inference(cnf_transformation,[],[f7])).
% 59.36/8.01  
% 59.36/8.01  fof(f55,plain,(
% 59.36/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 59.36/8.01    inference(definition_unfolding,[],[f33,f30,f30,f47])).
% 59.36/8.01  
% 59.36/8.01  fof(f3,axiom,(
% 59.36/8.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 59.36/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.36/8.01  
% 59.36/8.01  fof(f22,plain,(
% 59.36/8.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 59.36/8.01    inference(rectify,[],[f3])).
% 59.36/8.01  
% 59.36/8.01  fof(f29,plain,(
% 59.36/8.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 59.36/8.01    inference(cnf_transformation,[],[f22])).
% 59.36/8.01  
% 59.36/8.01  cnf(c_9,plain,
% 59.36/8.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 59.36/8.01      inference(cnf_transformation,[],[f57]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_136,plain,
% 59.36/8.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 59.36/8.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_3,plain,
% 59.36/8.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 59.36/8.01      inference(cnf_transformation,[],[f31]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_138,plain,
% 59.36/8.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 59.36/8.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_1939,plain,
% 59.36/8.01      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_136,c_138]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_0,plain,
% 59.36/8.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 59.36/8.01      inference(cnf_transformation,[],[f27]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_10,negated_conjecture,
% 59.36/8.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.36/8.01      inference(cnf_transformation,[],[f58]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_218,plain,
% 59.36/8.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_0,c_10]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_195419,plain,
% 59.36/8.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_1939,c_218]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_4,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 59.36/8.01      inference(cnf_transformation,[],[f54]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_7,plain,
% 59.36/8.01      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 59.36/8.01      inference(cnf_transformation,[],[f56]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_137,plain,
% 59.36/8.01      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 59.36/8.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_569,plain,
% 59.36/8.01      ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_4,c_137]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_6,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.36/8.01      inference(cnf_transformation,[],[f34]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_1,plain,
% 59.36/8.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 59.36/8.01      inference(cnf_transformation,[],[f28]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_262,plain,
% 59.36/8.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_578,plain,
% 59.36/8.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 59.36/8.01      inference(light_normalisation,[status(thm)],[c_569,c_262]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_1941,plain,
% 59.36/8.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_578,c_138]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_8,plain,
% 59.36/8.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 59.36/8.01      inference(cnf_transformation,[],[f36]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_143,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_795,plain,
% 59.36/8.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_6,c_143]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_5,plain,
% 59.36/8.01      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 59.36/8.01      inference(cnf_transformation,[],[f55]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_70,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 59.36/8.01      inference(theory_normalisation,[status(thm)],[c_5,c_8,c_1]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_831,plain,
% 59.36/8.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0),X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_795,c_70]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_142,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_836,plain,
% 59.36/8.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_795,c_142]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_837,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))),k1_xboole_0),k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_795,c_70]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_851,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))),k1_xboole_0),k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 59.36/8.01      inference(light_normalisation,[status(thm)],[c_837,c_4]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_337,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_725,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X1,X0) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_337,c_142]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_852,plain,
% 59.36/8.01      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0),X0) = X0 ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_851,c_725]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_853,plain,
% 59.36/8.01      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
% 59.36/8.01      inference(light_normalisation,[status(thm)],[c_852,c_262]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_857,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_831,c_836,c_853]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_2,plain,
% 59.36/8.01      ( k3_xboole_0(X0,X0) = X0 ),
% 59.36/8.01      inference(cnf_transformation,[],[f29]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_858,plain,
% 59.36/8.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 59.36/8.01      inference(light_normalisation,[status(thm)],[c_857,c_2,c_4]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_859,plain,
% 59.36/8.01      ( k5_xboole_0(X0,X0) = k3_xboole_0(k1_xboole_0,X0) ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_858,c_262]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_2318,plain,
% 59.36/8.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_1941,c_859]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_144,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_2449,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 59.36/8.01      inference(superposition,[status(thm)],[c_2318,c_144]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_2454,plain,
% 59.36/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_2449,c_6]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_195420,plain,
% 59.36/8.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.36/8.01      inference(demodulation,[status(thm)],[c_195419,c_2454]) ).
% 59.36/8.01  
% 59.36/8.01  cnf(c_195421,plain,
% 59.36/8.01      ( $false ),
% 59.36/8.01      inference(equality_resolution_simp,[status(thm)],[c_195420]) ).
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  % SZS output end CNFRefutation for theBenchmark.p
% 59.36/8.01  
% 59.36/8.01  ------                               Statistics
% 59.36/8.01  
% 59.36/8.01  ------ General
% 59.36/8.01  
% 59.36/8.01  abstr_ref_over_cycles:                  0
% 59.36/8.01  abstr_ref_under_cycles:                 0
% 59.36/8.01  gc_basic_clause_elim:                   0
% 59.36/8.01  forced_gc_time:                         0
% 59.36/8.01  parsing_time:                           0.007
% 59.36/8.01  unif_index_cands_time:                  0.
% 59.36/8.01  unif_index_add_time:                    0.
% 59.36/8.01  orderings_time:                         0.
% 59.36/8.01  out_proof_time:                         0.008
% 59.36/8.01  total_time:                             7.054
% 59.36/8.01  num_of_symbols:                         38
% 59.36/8.01  num_of_terms:                           351091
% 59.36/8.01  
% 59.36/8.01  ------ Preprocessing
% 59.36/8.01  
% 59.36/8.01  num_of_splits:                          0
% 59.36/8.01  num_of_split_atoms:                     0
% 59.36/8.01  num_of_reused_defs:                     0
% 59.36/8.01  num_eq_ax_congr_red:                    0
% 59.36/8.01  num_of_sem_filtered_clauses:            1
% 59.36/8.01  num_of_subtypes:                        0
% 59.36/8.01  monotx_restored_types:                  0
% 59.36/8.01  sat_num_of_epr_types:                   0
% 59.36/8.01  sat_num_of_non_cyclic_types:            0
% 59.36/8.01  sat_guarded_non_collapsed_types:        0
% 59.36/8.01  num_pure_diseq_elim:                    0
% 59.36/8.01  simp_replaced_by:                       0
% 59.36/8.01  res_preprocessed:                       46
% 59.36/8.01  prep_upred:                             0
% 59.36/8.01  prep_unflattend:                        4
% 59.36/8.01  smt_new_axioms:                         0
% 59.36/8.01  pred_elim_cands:                        1
% 59.36/8.01  pred_elim:                              0
% 59.36/8.01  pred_elim_cl:                           0
% 59.36/8.01  pred_elim_cycles:                       1
% 59.36/8.01  merged_defs:                            0
% 59.36/8.01  merged_defs_ncl:                        0
% 59.36/8.01  bin_hyper_res:                          0
% 59.36/8.01  prep_cycles:                            3
% 59.36/8.01  pred_elim_time:                         0.
% 59.36/8.01  splitting_time:                         0.
% 59.36/8.01  sem_filter_time:                        0.
% 59.36/8.01  monotx_time:                            0.001
% 59.36/8.01  subtype_inf_time:                       0.
% 59.36/8.01  
% 59.36/8.01  ------ Problem properties
% 59.36/8.01  
% 59.36/8.01  clauses:                                11
% 59.36/8.01  conjectures:                            1
% 59.36/8.01  epr:                                    0
% 59.36/8.01  horn:                                   11
% 59.36/8.01  ground:                                 1
% 59.36/8.01  unary:                                  10
% 59.36/8.01  binary:                                 1
% 59.36/8.01  lits:                                   12
% 59.36/8.01  lits_eq:                                9
% 59.36/8.01  fd_pure:                                0
% 59.36/8.01  fd_pseudo:                              0
% 59.36/8.01  fd_cond:                                0
% 59.36/8.01  fd_pseudo_cond:                         0
% 59.36/8.01  ac_symbols:                             1
% 59.36/8.01  
% 59.36/8.01  ------ Propositional Solver
% 59.36/8.01  
% 59.36/8.01  prop_solver_calls:                      30
% 59.36/8.01  prop_fast_solver_calls:                 740
% 59.36/8.01  smt_solver_calls:                       0
% 59.36/8.01  smt_fast_solver_calls:                  0
% 59.36/8.01  prop_num_of_clauses:                    28355
% 59.36/8.01  prop_preprocess_simplified:             24089
% 59.36/8.01  prop_fo_subsumed:                       0
% 59.36/8.01  prop_solver_time:                       0.
% 59.36/8.01  smt_solver_time:                        0.
% 59.36/8.01  smt_fast_solver_time:                   0.
% 59.36/8.01  prop_fast_solver_time:                  0.
% 59.36/8.01  prop_unsat_core_time:                   0.
% 59.36/8.01  
% 59.36/8.01  ------ QBF
% 59.36/8.01  
% 59.36/8.01  qbf_q_res:                              0
% 59.36/8.01  qbf_num_tautologies:                    0
% 59.36/8.01  qbf_prep_cycles:                        0
% 59.36/8.01  
% 59.36/8.01  ------ BMC1
% 59.36/8.01  
% 59.36/8.01  bmc1_current_bound:                     -1
% 59.36/8.01  bmc1_last_solved_bound:                 -1
% 59.36/8.01  bmc1_unsat_core_size:                   -1
% 59.36/8.01  bmc1_unsat_core_parents_size:           -1
% 59.36/8.01  bmc1_merge_next_fun:                    0
% 59.36/8.01  bmc1_unsat_core_clauses_time:           0.
% 59.36/8.01  
% 59.36/8.01  ------ Instantiation
% 59.36/8.01  
% 59.36/8.01  inst_num_of_clauses:                    4154
% 59.36/8.01  inst_num_in_passive:                    1137
% 59.36/8.01  inst_num_in_active:                     1350
% 59.36/8.01  inst_num_in_unprocessed:                1667
% 59.36/8.01  inst_num_of_loops:                      1650
% 59.36/8.01  inst_num_of_learning_restarts:          0
% 59.36/8.01  inst_num_moves_active_passive:          296
% 59.36/8.01  inst_lit_activity:                      0
% 59.36/8.01  inst_lit_activity_moves:                1
% 59.36/8.01  inst_num_tautologies:                   0
% 59.36/8.01  inst_num_prop_implied:                  0
% 59.36/8.01  inst_num_existing_simplified:           0
% 59.36/8.01  inst_num_eq_res_simplified:             0
% 59.36/8.01  inst_num_child_elim:                    0
% 59.36/8.01  inst_num_of_dismatching_blockings:      5750
% 59.36/8.01  inst_num_of_non_proper_insts:           4396
% 59.36/8.01  inst_num_of_duplicates:                 0
% 59.36/8.01  inst_inst_num_from_inst_to_res:         0
% 59.36/8.01  inst_dismatching_checking_time:         0.
% 59.36/8.01  
% 59.36/8.01  ------ Resolution
% 59.36/8.01  
% 59.36/8.01  res_num_of_clauses:                     0
% 59.36/8.01  res_num_in_passive:                     0
% 59.36/8.01  res_num_in_active:                      0
% 59.36/8.01  res_num_of_loops:                       49
% 59.36/8.01  res_forward_subset_subsumed:            1454
% 59.36/8.01  res_backward_subset_subsumed:           0
% 59.36/8.01  res_forward_subsumed:                   0
% 59.36/8.01  res_backward_subsumed:                  0
% 59.36/8.01  res_forward_subsumption_resolution:     0
% 59.36/8.01  res_backward_subsumption_resolution:    0
% 59.36/8.01  res_clause_to_clause_subsumption:       579690
% 59.36/8.01  res_orphan_elimination:                 0
% 59.36/8.01  res_tautology_del:                      308
% 59.36/8.01  res_num_eq_res_simplified:              0
% 59.36/8.01  res_num_sel_changes:                    0
% 59.36/8.01  res_moves_from_active_to_pass:          0
% 59.36/8.01  
% 59.36/8.01  ------ Superposition
% 59.36/8.01  
% 59.36/8.01  sup_time_total:                         0.
% 59.36/8.01  sup_time_generating:                    0.
% 59.36/8.01  sup_time_sim_full:                      0.
% 59.36/8.01  sup_time_sim_immed:                     0.
% 59.36/8.01  
% 59.36/8.01  sup_num_of_clauses:                     12892
% 59.36/8.01  sup_num_in_active:                      233
% 59.36/8.01  sup_num_in_passive:                     12659
% 59.36/8.01  sup_num_of_loops:                       329
% 59.36/8.01  sup_fw_superposition:                   49487
% 59.36/8.01  sup_bw_superposition:                   46803
% 59.36/8.01  sup_immediate_simplified:               53614
% 59.36/8.01  sup_given_eliminated:                   11
% 59.36/8.01  comparisons_done:                       0
% 59.36/8.01  comparisons_avoided:                    0
% 59.36/8.01  
% 59.36/8.01  ------ Simplifications
% 59.36/8.01  
% 59.36/8.01  
% 59.36/8.01  sim_fw_subset_subsumed:                 0
% 59.36/8.01  sim_bw_subset_subsumed:                 0
% 59.36/8.01  sim_fw_subsumed:                        6778
% 59.36/8.01  sim_bw_subsumed:                        145
% 59.36/8.01  sim_fw_subsumption_res:                 0
% 59.36/8.01  sim_bw_subsumption_res:                 0
% 59.36/8.01  sim_tautology_del:                      0
% 59.36/8.01  sim_eq_tautology_del:                   12617
% 59.36/8.01  sim_eq_res_simp:                        0
% 59.36/8.01  sim_fw_demodulated:                     48871
% 59.36/8.01  sim_bw_demodulated:                     670
% 59.36/8.01  sim_light_normalised:                   18570
% 59.36/8.01  sim_joinable_taut:                      1075
% 59.36/8.01  sim_joinable_simp:                      0
% 59.36/8.01  sim_ac_normalised:                      0
% 59.36/8.01  sim_smt_subsumption:                    0
% 59.36/8.01  
%------------------------------------------------------------------------------
