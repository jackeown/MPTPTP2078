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
% DateTime   : Thu Dec  3 11:26:48 EST 2020

% Result     : Theorem 11.29s
% Output     : CNFRefutation 11.29s
% Verified   : 
% Statistics : Number of formulae       :  105 (4985 expanded)
%              Number of clauses        :   57 (2185 expanded)
%              Number of leaves         :   17 (1239 expanded)
%              Depth                    :   25
%              Number of atoms          :  106 (4986 expanded)
%              Number of equality atoms :  105 (4985 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f17])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f20])).

fof(f37,plain,(
    k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f48,plain,(
    k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(definition_unfolding,[],[f37,f39,f42])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f27,f38])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) ),
    inference(definition_unfolding,[],[f33,f41,f39])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))) ),
    inference(definition_unfolding,[],[f34,f27,f40,f39])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))),k1_tarski(X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) ),
    inference(definition_unfolding,[],[f32,f40,f41])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_175,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_240,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3,c_175])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_249,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_240,c_1])).

cnf(c_255,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_249])).

cnf(c_632,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_255,c_249])).

cnf(c_640,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_632,c_255])).

cnf(c_866,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_640,c_249])).

cnf(c_870,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_640,c_0])).

cnf(c_885,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_866,c_870])).

cnf(c_1215,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_255,c_885])).

cnf(c_1252,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1215,c_885])).

cnf(c_2,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_408,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_1414,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1252,c_408])).

cnf(c_1416,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(demodulation,[status(thm)],[c_1414,c_2,c_249])).

cnf(c_1885,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_3,c_1416])).

cnf(c_1869,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_1416])).

cnf(c_4713,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_1885,c_1869])).

cnf(c_1210,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_249,c_885])).

cnf(c_1261,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1210,c_885])).

cnf(c_5073,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_4713,c_1261])).

cnf(c_1211,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_175,c_885])).

cnf(c_1258,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1211,c_885])).

cnf(c_1471,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1258])).

cnf(c_1677,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_249,c_1471])).

cnf(c_2033,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_1869,c_1677])).

cnf(c_2031,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1869,c_1677])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_44,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
    inference(demodulation,[status(thm)],[c_7,c_4])).

cnf(c_50,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) ),
    inference(light_normalisation,[status(thm)],[c_6,c_44])).

cnf(c_51,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) ),
    inference(demodulation,[status(thm)],[c_50,c_4])).

cnf(c_53,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
    inference(demodulation,[status(thm)],[c_51,c_44])).

cnf(c_8,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_46,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(demodulation,[status(thm)],[c_44,c_8])).

cnf(c_54,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(demodulation,[status(thm)],[c_51,c_46])).

cnf(c_64,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_9,c_53,c_54])).

cnf(c_103,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_0,c_64])).

cnf(c_1838,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_1416,c_103])).

cnf(c_3160,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK7)),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_0,c_1838])).

cnf(c_5338,plain,
    ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK7)),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_2031,c_3160])).

cnf(c_5630,plain,
    ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK7)),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_2031,c_5338])).

cnf(c_5870,plain,
    ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5))))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_1869,c_5630])).

cnf(c_9667,plain,
    ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5)),k1_tarski(sK6)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_2033,c_5870])).

cnf(c_12521,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5)),k1_tarski(sK6)),k1_tarski(sK1))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_2033,c_9667])).

cnf(c_12879,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6))),k1_tarski(sK1))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_1869,c_12521])).

cnf(c_32210,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_5073,c_12879])).

cnf(c_5,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_60,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(light_normalisation,[status(thm)],[c_5,c_4])).

cnf(c_61,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(demodulation,[status(thm)],[c_60,c_4])).

cnf(c_32213,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_32210,c_54,c_61])).

cnf(c_32214,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_32213])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:50:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.29/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.29/1.99  
% 11.29/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.29/1.99  
% 11.29/1.99  ------  iProver source info
% 11.29/1.99  
% 11.29/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.29/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.29/1.99  git: non_committed_changes: false
% 11.29/1.99  git: last_make_outside_of_git: false
% 11.29/1.99  
% 11.29/1.99  ------ 
% 11.29/1.99  ------ Parsing...
% 11.29/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.29/1.99  
% 11.29/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.29/1.99  
% 11.29/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.29/1.99  
% 11.29/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.29/1.99  ------ Proving...
% 11.29/1.99  ------ Problem Properties 
% 11.29/1.99  
% 11.29/1.99  
% 11.29/1.99  clauses                                 10
% 11.29/1.99  conjectures                             1
% 11.29/1.99  EPR                                     0
% 11.29/1.99  Horn                                    10
% 11.29/1.99  unary                                   10
% 11.29/1.99  binary                                  0
% 11.29/1.99  lits                                    10
% 11.29/1.99  lits eq                                 10
% 11.29/1.99  fd_pure                                 0
% 11.29/1.99  fd_pseudo                               0
% 11.29/1.99  fd_cond                                 0
% 11.29/1.99  fd_pseudo_cond                          0
% 11.29/1.99  AC symbols                              0
% 11.29/1.99  
% 11.29/1.99  ------ Input Options Time Limit: Unbounded
% 11.29/1.99  
% 11.29/1.99  
% 11.29/1.99  ------ 
% 11.29/1.99  Current options:
% 11.29/1.99  ------ 
% 11.29/1.99  
% 11.29/1.99  
% 11.29/1.99  
% 11.29/1.99  
% 11.29/1.99  ------ Proving...
% 11.29/1.99  
% 11.29/1.99  
% 11.29/1.99  % SZS status Theorem for theBenchmark.p
% 11.29/1.99  
% 11.29/1.99   Resolution empty clause
% 11.29/1.99  
% 11.29/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.29/1.99  
% 11.29/1.99  fof(f4,axiom,(
% 11.29/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f25,plain,(
% 11.29/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 11.29/1.99    inference(cnf_transformation,[],[f4])).
% 11.29/1.99  
% 11.29/1.99  fof(f1,axiom,(
% 11.29/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f22,plain,(
% 11.29/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f1])).
% 11.29/1.99  
% 11.29/1.99  fof(f2,axiom,(
% 11.29/1.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f18,plain,(
% 11.29/1.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 11.29/1.99    inference(rectify,[],[f2])).
% 11.29/1.99  
% 11.29/1.99  fof(f23,plain,(
% 11.29/1.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 11.29/1.99    inference(cnf_transformation,[],[f18])).
% 11.29/1.99  
% 11.29/1.99  fof(f3,axiom,(
% 11.29/1.99    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f24,plain,(
% 11.29/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 11.29/1.99    inference(cnf_transformation,[],[f3])).
% 11.29/1.99  
% 11.29/1.99  fof(f16,conjecture,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f17,negated_conjecture,(
% 11.29/1.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.29/1.99    inference(negated_conjecture,[],[f16])).
% 11.29/1.99  
% 11.29/1.99  fof(f19,plain,(
% 11.29/1.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.29/1.99    inference(ennf_transformation,[],[f17])).
% 11.29/1.99  
% 11.29/1.99  fof(f20,plain,(
% 11.29/1.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) => k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 11.29/1.99    introduced(choice_axiom,[])).
% 11.29/1.99  
% 11.29/1.99  fof(f21,plain,(
% 11.29/1.99    k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 11.29/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f20])).
% 11.29/1.99  
% 11.29/1.99  fof(f37,plain,(
% 11.29/1.99    k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 11.29/1.99    inference(cnf_transformation,[],[f21])).
% 11.29/1.99  
% 11.29/1.99  fof(f14,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f35,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f14])).
% 11.29/1.99  
% 11.29/1.99  fof(f5,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f26,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f5])).
% 11.29/1.99  
% 11.29/1.99  fof(f7,axiom,(
% 11.29/1.99    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f28,plain,(
% 11.29/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f7])).
% 11.29/1.99  
% 11.29/1.99  fof(f6,axiom,(
% 11.29/1.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f27,plain,(
% 11.29/1.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f6])).
% 11.29/1.99  
% 11.29/1.99  fof(f38,plain,(
% 11.29/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k1_enumset1(X0,X1,X2)) )),
% 11.29/1.99    inference(definition_unfolding,[],[f28,f27])).
% 11.29/1.99  
% 11.29/1.99  fof(f39,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.29/1.99    inference(definition_unfolding,[],[f26,f38])).
% 11.29/1.99  
% 11.29/1.99  fof(f42,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.29/1.99    inference(definition_unfolding,[],[f35,f39])).
% 11.29/1.99  
% 11.29/1.99  fof(f48,plain,(
% 11.29/1.99    k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))),
% 11.29/1.99    inference(definition_unfolding,[],[f37,f39,f42])).
% 11.29/1.99  
% 11.29/1.99  fof(f12,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f33,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f12])).
% 11.29/1.99  
% 11.29/1.99  fof(f10,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f31,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f10])).
% 11.29/1.99  
% 11.29/1.99  fof(f8,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f29,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f8])).
% 11.29/1.99  
% 11.29/1.99  fof(f40,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 11.29/1.99    inference(definition_unfolding,[],[f29,f27,f38])).
% 11.29/1.99  
% 11.29/1.99  fof(f41,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 11.29/1.99    inference(definition_unfolding,[],[f31,f40])).
% 11.29/1.99  
% 11.29/1.99  fof(f45,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))))) )),
% 11.29/1.99    inference(definition_unfolding,[],[f33,f41,f39])).
% 11.29/1.99  
% 11.29/1.99  fof(f13,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f34,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f13])).
% 11.29/1.99  
% 11.29/1.99  fof(f46,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) )),
% 11.29/1.99    inference(definition_unfolding,[],[f34,f27,f40,f39])).
% 11.29/1.99  
% 11.29/1.99  fof(f9,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f30,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f9])).
% 11.29/1.99  
% 11.29/1.99  fof(f43,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))))) )),
% 11.29/1.99    inference(definition_unfolding,[],[f30,f40])).
% 11.29/1.99  
% 11.29/1.99  fof(f15,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f36,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f15])).
% 11.29/1.99  
% 11.29/1.99  fof(f47,plain,(
% 11.29/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))) )),
% 11.29/1.99    inference(definition_unfolding,[],[f36,f42])).
% 11.29/1.99  
% 11.29/1.99  fof(f11,axiom,(
% 11.29/1.99    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 11.29/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/1.99  
% 11.29/1.99  fof(f32,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 11.29/1.99    inference(cnf_transformation,[],[f11])).
% 11.29/1.99  
% 11.29/1.99  fof(f44,plain,(
% 11.29/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))),k1_tarski(X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))))) )),
% 11.29/1.99    inference(definition_unfolding,[],[f32,f40,f41])).
% 11.29/1.99  
% 11.29/1.99  cnf(c_3,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.29/1.99      inference(cnf_transformation,[],[f25]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_0,plain,
% 11.29/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(cnf_transformation,[],[f22]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_175,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_240,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_3,c_175]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1,plain,
% 11.29/1.99      ( k2_xboole_0(X0,X0) = X0 ),
% 11.29/1.99      inference(cnf_transformation,[],[f23]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_249,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_240,c_1]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_255,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_0,c_249]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_632,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_255,c_249]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_640,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_632,c_255]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_866,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_640,c_249]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_870,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_640,c_0]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_885,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(light_normalisation,[status(thm)],[c_866,c_870]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1215,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_255,c_885]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1252,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(light_normalisation,[status(thm)],[c_1215,c_885]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_2,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 11.29/1.99      inference(cnf_transformation,[],[f24]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_408,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1414,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X0,X1)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_1252,c_408]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1416,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_1414,c_2,c_249]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1885,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_3,c_1416]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1869,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_0,c_1416]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_4713,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_1885,c_1869]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1210,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_249,c_885]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1261,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(light_normalisation,[status(thm)],[c_1210,c_885]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_5073,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_4713,c_1261]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1211,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_175,c_885]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1258,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.29/1.99      inference(light_normalisation,[status(thm)],[c_1211,c_885]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1471,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_0,c_1258]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1677,plain,
% 11.29/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_249,c_1471]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_2033,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_1869,c_1677]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_2031,plain,
% 11.29/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_1869,c_1677]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_9,negated_conjecture,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
% 11.29/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_6,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
% 11.29/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_7,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
% 11.29/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_4,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
% 11.29/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_44,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_7,c_4]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_50,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) ),
% 11.29/1.99      inference(light_normalisation,[status(thm)],[c_6,c_44]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_51,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_50,c_4]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_53,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_51,c_44]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_8,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
% 11.29/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_46,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_44,c_8]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_54,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_51,c_46]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_64,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_9,c_53,c_54]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_103,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_0,c_64]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_1838,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_1416,c_103]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_3160,plain,
% 11.29/1.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK7)),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_0,c_1838]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_5338,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK7)),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_2031,c_3160]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_5630,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK7)),k2_enumset1(sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_2031,c_5338]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_5870,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5))))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_1869,c_5630]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_9667,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5)),k1_tarski(sK6)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_2033,c_5870]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_12521,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5)),k1_tarski(sK6)),k1_tarski(sK1))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_2033,c_9667]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_12879,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6))),k1_tarski(sK1))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(superposition,[status(thm)],[c_1869,c_12521]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_32210,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_5073,c_12879]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_5,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))),k1_tarski(X5)) ),
% 11.29/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_60,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) ),
% 11.29/1.99      inference(light_normalisation,[status(thm)],[c_5,c_4]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_61,plain,
% 11.29/1.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_60,c_4]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_32213,plain,
% 11.29/1.99      ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
% 11.29/1.99      inference(demodulation,[status(thm)],[c_32210,c_54,c_61]) ).
% 11.29/1.99  
% 11.29/1.99  cnf(c_32214,plain,
% 11.29/1.99      ( $false ),
% 11.29/1.99      inference(equality_resolution_simp,[status(thm)],[c_32213]) ).
% 11.29/1.99  
% 11.29/1.99  
% 11.29/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.29/1.99  
% 11.29/1.99  ------                               Statistics
% 11.29/1.99  
% 11.29/1.99  ------ Selected
% 11.29/1.99  
% 11.29/1.99  total_time:                             1.241
% 11.29/1.99  
%------------------------------------------------------------------------------
