%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:51 EST 2020

% Result     : Theorem 23.78s
% Output     : CNFRefutation 23.78s
% Verified   : 
% Statistics : Number of formulae       :  177 (12648 expanded)
%              Number of clauses        :  129 (3021 expanded)
%              Number of leaves         :   16 (3647 expanded)
%              Depth                    :   31
%              Number of atoms          :  178 (12649 expanded)
%              Number of equality atoms :  177 (12648 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f40,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f36,f36])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7)) ),
    inference(definition_unfolding,[],[f26,f35,f37])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f22,f30,f30])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f21,f30,f30])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).

fof(f34,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f34,f30,f30])).

cnf(c_0,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_27,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36) = k1_tarski(X0_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k1_tarski(X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_216,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_27,c_22])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_267,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X1_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_216,c_26])).

cnf(c_2,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_238,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X2_36)) = k3_enumset1(X0_36,X2_36,X2_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_25,c_26])).

cnf(c_243,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X2_36,X2_36,X2_36,X1_36) ),
    inference(demodulation,[status(thm)],[c_238,c_26,c_216])).

cnf(c_588,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X2_36) = k3_enumset1(X0_36,X2_36,X2_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_267,c_243])).

cnf(c_244,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(demodulation,[status(thm)],[c_216,c_25])).

cnf(c_6,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7)) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X5_36,X6_36,X7_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_304,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_244,c_21])).

cnf(c_320,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X1_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) ),
    inference(demodulation,[status(thm)],[c_304,c_244])).

cnf(c_255,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)) = k1_tarski(X0_36) ),
    inference(superposition,[status(thm)],[c_216,c_27])).

cnf(c_256,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_216,c_21])).

cnf(c_271,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(demodulation,[status(thm)],[c_256,c_216])).

cnf(c_272,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) ),
    inference(demodulation,[status(thm)],[c_255,c_271])).

cnf(c_7,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_39,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(light_normalisation,[status(thm)],[c_20,c_27])).

cnf(c_273,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(light_normalisation,[status(thm)],[c_272,c_39])).

cnf(c_321,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(light_normalisation,[status(thm)],[c_320,c_273])).

cnf(c_322,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_321,c_39,c_255])).

cnf(c_734,plain,
    ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X2_36) = k3_enumset1(X1_36,X2_36,X2_36,X2_36,X0_36) ),
    inference(superposition,[status(thm)],[c_588,c_322])).

cnf(c_4,plain,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X3_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_265,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_216,c_23])).

cnf(c_344,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_265,c_26])).

cnf(c_1150,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) = k3_enumset1(X0_36,X1_36,X1_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_344,c_267])).

cnf(c_1623,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) = k3_enumset1(X2_36,X0_36,X2_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_734,c_1150])).

cnf(c_163,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k3_enumset1(X2_36,X3_36,X4_36,X5_36,X6_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36),k3_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36)) ),
    inference(superposition,[status(thm)],[c_23,c_21])).

cnf(c_952,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k3_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X3_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X2_36,X4_36,X5_36,X6_36)) ),
    inference(light_normalisation,[status(thm)],[c_163,c_244])).

cnf(c_4988,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X0_36,X1_36),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X1_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_1623,c_952])).

cnf(c_41,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
    inference(superposition,[status(thm)],[c_23,c_23])).

cnf(c_732,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X0_36) = k3_enumset1(X0_36,X0_36,X1_36,X0_36,X0_36) ),
    inference(superposition,[status(thm)],[c_588,c_41])).

cnf(c_317,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_244,c_41])).

cnf(c_737,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(light_normalisation,[status(thm)],[c_732,c_317])).

cnf(c_791,plain,
    ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_737,c_322])).

cnf(c_268,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_216,c_41])).

cnf(c_364,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X1_36,X0_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_268,c_22])).

cnf(c_337,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_265,c_22])).

cnf(c_1233,plain,
    ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X2_36) = k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_364,c_337])).

cnf(c_730,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_588,c_216])).

cnf(c_764,plain,
    ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_730,c_322])).

cnf(c_2416,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_1233,c_764])).

cnf(c_3,plain,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X3_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_50,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X2_36,X1_36,X3_36) ),
    inference(superposition,[status(thm)],[c_24,c_23])).

cnf(c_2540,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_2416,c_50])).

cnf(c_2737,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_2540,c_21])).

cnf(c_2767,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(demodulation,[status(thm)],[c_2737,c_2540])).

cnf(c_241,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X3_36,X4_36,X2_36) ),
    inference(superposition,[status(thm)],[c_41,c_26])).

cnf(c_2768,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X3_36,X4_36,X2_36) ),
    inference(light_normalisation,[status(thm)],[c_2767,c_241,c_255])).

cnf(c_5084,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X3_36,X4_36,X2_36) ),
    inference(light_normalisation,[status(thm)],[c_4988,c_791,c_2768])).

cnf(c_2415,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_1233,c_791])).

cnf(c_2476,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X1_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2415,c_22])).

cnf(c_4374,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
    inference(superposition,[status(thm)],[c_2476,c_21])).

cnf(c_313,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_244,c_23])).

cnf(c_260,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_216,c_22])).

cnf(c_535,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
    inference(superposition,[status(thm)],[c_260,c_21])).

cnf(c_564,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
    inference(light_normalisation,[status(thm)],[c_535,c_27])).

cnf(c_4448,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X0_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X1_36),k3_enumset1(X0_36,X2_36,X3_36,X4_36,X5_36)) ),
    inference(light_normalisation,[status(thm)],[c_4374,c_313,c_564])).

cnf(c_5085,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X0_36,X1_36,X4_36,X2_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_5084,c_39,c_255,c_4448])).

cnf(c_176,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X6_36,X7_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) ),
    inference(superposition,[status(thm)],[c_23,c_21])).

cnf(c_10661,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X1_36)) ),
    inference(superposition,[status(thm)],[c_27,c_176])).

cnf(c_448,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
    inference(superposition,[status(thm)],[c_41,c_39])).

cnf(c_11511,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X1_36)) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
    inference(light_normalisation,[status(thm)],[c_10661,c_27,c_448])).

cnf(c_102704,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X1_36) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
    inference(superposition,[status(thm)],[c_11511,c_26])).

cnf(c_180,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X6_36,X5_36,X7_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) ),
    inference(superposition,[status(thm)],[c_50,c_21])).

cnf(c_23169,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_2540,c_180])).

cnf(c_222,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k1_tarski(X4_36)) = k3_enumset1(X0_36,X3_36,X1_36,X2_36,X4_36) ),
    inference(superposition,[status(thm)],[c_23,c_22])).

cnf(c_17136,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X0_36,X3_36,X1_36,X2_36,X4_36) ),
    inference(superposition,[status(thm)],[c_222,c_22])).

cnf(c_370,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X2_36,X1_36,X1_36) ),
    inference(superposition,[status(thm)],[c_268,c_26])).

cnf(c_1315,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X1_36,X1_36) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_370,c_344])).

cnf(c_1672,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_1150,c_737])).

cnf(c_3632,plain,
    ( k3_enumset1(X0_36,X1_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_1315,c_1672])).

cnf(c_17660,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_17136,c_3632])).

cnf(c_23261,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_17660,c_180])).

cnf(c_23853,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X0_36,X0_36,X2_36,X3_36,X4_36)) ),
    inference(light_normalisation,[status(thm)],[c_23261,c_244])).

cnf(c_2484,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_2415,c_50])).

cnf(c_2642,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2484,c_26])).

cnf(c_177,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) = k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X5_36,X7_36,X6_36)) ),
    inference(superposition,[status(thm)],[c_24,c_21])).

cnf(c_15940,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X2_36,X2_36,X3_36,X5_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_2642,c_177])).

cnf(c_2485,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_2415,c_41])).

cnf(c_2697,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_2485,c_26])).

cnf(c_15944,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X2_36,X1_36,X3_36,X5_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_2697,c_177])).

cnf(c_2541,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
    inference(superposition,[status(thm)],[c_2416,c_41])).

cnf(c_2806,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X2_36,X1_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2541,c_26])).

cnf(c_15948,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X2_36,X1_36),k3_enumset1(X1_36,X2_36,X3_36,X5_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_2806,c_177])).

cnf(c_6598,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) ),
    inference(superposition,[status(thm)],[c_2642,c_21])).

cnf(c_6673,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) ),
    inference(light_normalisation,[status(thm)],[c_6598,c_2540])).

cnf(c_2636,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2484,c_22])).

cnf(c_6434,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X2_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X1_36,X3_36,X4_36,X5_36)) ),
    inference(superposition,[status(thm)],[c_2636,c_952])).

cnf(c_6511,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X1_36),k3_enumset1(X2_36,X0_36,X3_36,X4_36,X5_36)) ),
    inference(light_normalisation,[status(thm)],[c_6434,c_564])).

cnf(c_6674,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X2_36,X1_36,X3_36,X4_36,X5_36)) ),
    inference(demodulation,[status(thm)],[c_6673,c_6511])).

cnf(c_16109,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X2_36,X1_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X5_36,X4_36)) ),
    inference(light_normalisation,[status(thm)],[c_15948,c_6674])).

cnf(c_16116,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
    inference(demodulation,[status(thm)],[c_15944,c_16109])).

cnf(c_16119,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X5_36,X4_36)) ),
    inference(demodulation,[status(thm)],[c_15940,c_16116])).

cnf(c_16120,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X1_36),k3_enumset1(X0_36,X2_36,X3_36,X5_36,X4_36)) ),
    inference(light_normalisation,[status(thm)],[c_16119,c_2540])).

cnf(c_1673,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_1150,c_730])).

cnf(c_3631,plain,
    ( k3_enumset1(X0_36,X1_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_1315,c_1673])).

cnf(c_17661,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
    inference(superposition,[status(thm)],[c_17136,c_3631])).

cnf(c_18338,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_17661,c_21])).

cnf(c_15918,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X4_36,X3_36)) ),
    inference(superposition,[status(thm)],[c_1672,c_177])).

cnf(c_1709,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_1672,c_21])).

cnf(c_386,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_313,c_21])).

cnf(c_402,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(demodulation,[status(thm)],[c_386,c_313])).

cnf(c_333,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(superposition,[status(thm)],[c_265,c_21])).

cnf(c_348,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
    inference(demodulation,[status(thm)],[c_333,c_265])).

cnf(c_349,plain,
    ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(light_normalisation,[status(thm)],[c_348,c_255,c_273])).

cnf(c_403,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(light_normalisation,[status(thm)],[c_402,c_255,c_349])).

cnf(c_1727,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_1709,c_403])).

cnf(c_16158,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X4_36,X3_36) ),
    inference(light_normalisation,[status(thm)],[c_15918,c_1727])).

cnf(c_18390,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X0_36,X0_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X4_36,X3_36) ),
    inference(light_normalisation,[status(thm)],[c_18338,c_244,c_16158])).

cnf(c_23854,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X4_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_23853,c_16120,c_18390])).

cnf(c_23998,plain,
    ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X4_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_23169,c_23854])).

cnf(c_23999,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X1_36,X0_36,X4_36,X3_36,X2_36) ),
    inference(light_normalisation,[status(thm)],[c_23998,c_27,c_241])).

cnf(c_8,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_17144,plain,
    ( k3_enumset1(sK1,sK0,sK2,sK1,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_17136,c_19])).

cnf(c_24646,plain,
    ( k3_enumset1(sK0,sK1,sK3,sK1,sK2) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_23999,c_17144])).

cnf(c_73146,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK1) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_5085,c_24646])).

cnf(c_103220,plain,
    ( k3_enumset1(sK0,sK0,sK2,sK3,sK1) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_102704,c_73146])).

cnf(c_105682,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5085,c_103220])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.78/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.78/3.50  
% 23.78/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.78/3.50  
% 23.78/3.50  ------  iProver source info
% 23.78/3.50  
% 23.78/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.78/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.78/3.50  git: non_committed_changes: false
% 23.78/3.50  git: last_make_outside_of_git: false
% 23.78/3.50  
% 23.78/3.50  ------ 
% 23.78/3.50  
% 23.78/3.50  ------ Input Options
% 23.78/3.50  
% 23.78/3.50  --out_options                           all
% 23.78/3.50  --tptp_safe_out                         true
% 23.78/3.50  --problem_path                          ""
% 23.78/3.50  --include_path                          ""
% 23.78/3.50  --clausifier                            res/vclausify_rel
% 23.78/3.50  --clausifier_options                    ""
% 23.78/3.50  --stdin                                 false
% 23.78/3.50  --stats_out                             all
% 23.78/3.50  
% 23.78/3.50  ------ General Options
% 23.78/3.50  
% 23.78/3.50  --fof                                   false
% 23.78/3.50  --time_out_real                         305.
% 23.78/3.50  --time_out_virtual                      -1.
% 23.78/3.50  --symbol_type_check                     false
% 23.78/3.50  --clausify_out                          false
% 23.78/3.50  --sig_cnt_out                           false
% 23.78/3.50  --trig_cnt_out                          false
% 23.78/3.50  --trig_cnt_out_tolerance                1.
% 23.78/3.50  --trig_cnt_out_sk_spl                   false
% 23.78/3.50  --abstr_cl_out                          false
% 23.78/3.50  
% 23.78/3.50  ------ Global Options
% 23.78/3.50  
% 23.78/3.50  --schedule                              default
% 23.78/3.50  --add_important_lit                     false
% 23.78/3.50  --prop_solver_per_cl                    1000
% 23.78/3.50  --min_unsat_core                        false
% 23.78/3.50  --soft_assumptions                      false
% 23.78/3.50  --soft_lemma_size                       3
% 23.78/3.50  --prop_impl_unit_size                   0
% 23.78/3.50  --prop_impl_unit                        []
% 23.78/3.50  --share_sel_clauses                     true
% 23.78/3.50  --reset_solvers                         false
% 23.78/3.50  --bc_imp_inh                            [conj_cone]
% 23.78/3.50  --conj_cone_tolerance                   3.
% 23.78/3.50  --extra_neg_conj                        none
% 23.78/3.50  --large_theory_mode                     true
% 23.78/3.50  --prolific_symb_bound                   200
% 23.78/3.50  --lt_threshold                          2000
% 23.78/3.50  --clause_weak_htbl                      true
% 23.78/3.50  --gc_record_bc_elim                     false
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing Options
% 23.78/3.50  
% 23.78/3.50  --preprocessing_flag                    true
% 23.78/3.50  --time_out_prep_mult                    0.1
% 23.78/3.50  --splitting_mode                        input
% 23.78/3.50  --splitting_grd                         true
% 23.78/3.50  --splitting_cvd                         false
% 23.78/3.50  --splitting_cvd_svl                     false
% 23.78/3.50  --splitting_nvd                         32
% 23.78/3.50  --sub_typing                            true
% 23.78/3.50  --prep_gs_sim                           true
% 23.78/3.50  --prep_unflatten                        true
% 23.78/3.50  --prep_res_sim                          true
% 23.78/3.50  --prep_upred                            true
% 23.78/3.50  --prep_sem_filter                       exhaustive
% 23.78/3.50  --prep_sem_filter_out                   false
% 23.78/3.50  --pred_elim                             true
% 23.78/3.50  --res_sim_input                         true
% 23.78/3.50  --eq_ax_congr_red                       true
% 23.78/3.50  --pure_diseq_elim                       true
% 23.78/3.50  --brand_transform                       false
% 23.78/3.50  --non_eq_to_eq                          false
% 23.78/3.50  --prep_def_merge                        true
% 23.78/3.50  --prep_def_merge_prop_impl              false
% 23.78/3.50  --prep_def_merge_mbd                    true
% 23.78/3.50  --prep_def_merge_tr_red                 false
% 23.78/3.50  --prep_def_merge_tr_cl                  false
% 23.78/3.50  --smt_preprocessing                     true
% 23.78/3.50  --smt_ac_axioms                         fast
% 23.78/3.50  --preprocessed_out                      false
% 23.78/3.50  --preprocessed_stats                    false
% 23.78/3.50  
% 23.78/3.50  ------ Abstraction refinement Options
% 23.78/3.50  
% 23.78/3.50  --abstr_ref                             []
% 23.78/3.50  --abstr_ref_prep                        false
% 23.78/3.50  --abstr_ref_until_sat                   false
% 23.78/3.50  --abstr_ref_sig_restrict                funpre
% 23.78/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.78/3.50  --abstr_ref_under                       []
% 23.78/3.50  
% 23.78/3.50  ------ SAT Options
% 23.78/3.50  
% 23.78/3.50  --sat_mode                              false
% 23.78/3.50  --sat_fm_restart_options                ""
% 23.78/3.50  --sat_gr_def                            false
% 23.78/3.50  --sat_epr_types                         true
% 23.78/3.50  --sat_non_cyclic_types                  false
% 23.78/3.50  --sat_finite_models                     false
% 23.78/3.50  --sat_fm_lemmas                         false
% 23.78/3.50  --sat_fm_prep                           false
% 23.78/3.50  --sat_fm_uc_incr                        true
% 23.78/3.50  --sat_out_model                         small
% 23.78/3.50  --sat_out_clauses                       false
% 23.78/3.50  
% 23.78/3.50  ------ QBF Options
% 23.78/3.50  
% 23.78/3.50  --qbf_mode                              false
% 23.78/3.50  --qbf_elim_univ                         false
% 23.78/3.50  --qbf_dom_inst                          none
% 23.78/3.50  --qbf_dom_pre_inst                      false
% 23.78/3.50  --qbf_sk_in                             false
% 23.78/3.50  --qbf_pred_elim                         true
% 23.78/3.50  --qbf_split                             512
% 23.78/3.50  
% 23.78/3.50  ------ BMC1 Options
% 23.78/3.50  
% 23.78/3.50  --bmc1_incremental                      false
% 23.78/3.50  --bmc1_axioms                           reachable_all
% 23.78/3.50  --bmc1_min_bound                        0
% 23.78/3.50  --bmc1_max_bound                        -1
% 23.78/3.50  --bmc1_max_bound_default                -1
% 23.78/3.50  --bmc1_symbol_reachability              true
% 23.78/3.50  --bmc1_property_lemmas                  false
% 23.78/3.50  --bmc1_k_induction                      false
% 23.78/3.50  --bmc1_non_equiv_states                 false
% 23.78/3.50  --bmc1_deadlock                         false
% 23.78/3.50  --bmc1_ucm                              false
% 23.78/3.50  --bmc1_add_unsat_core                   none
% 23.78/3.50  --bmc1_unsat_core_children              false
% 23.78/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.78/3.50  --bmc1_out_stat                         full
% 23.78/3.50  --bmc1_ground_init                      false
% 23.78/3.50  --bmc1_pre_inst_next_state              false
% 23.78/3.50  --bmc1_pre_inst_state                   false
% 23.78/3.50  --bmc1_pre_inst_reach_state             false
% 23.78/3.50  --bmc1_out_unsat_core                   false
% 23.78/3.50  --bmc1_aig_witness_out                  false
% 23.78/3.50  --bmc1_verbose                          false
% 23.78/3.50  --bmc1_dump_clauses_tptp                false
% 23.78/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.78/3.50  --bmc1_dump_file                        -
% 23.78/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.78/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.78/3.50  --bmc1_ucm_extend_mode                  1
% 23.78/3.50  --bmc1_ucm_init_mode                    2
% 23.78/3.50  --bmc1_ucm_cone_mode                    none
% 23.78/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.78/3.50  --bmc1_ucm_relax_model                  4
% 23.78/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.78/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.78/3.50  --bmc1_ucm_layered_model                none
% 23.78/3.50  --bmc1_ucm_max_lemma_size               10
% 23.78/3.50  
% 23.78/3.50  ------ AIG Options
% 23.78/3.50  
% 23.78/3.50  --aig_mode                              false
% 23.78/3.50  
% 23.78/3.50  ------ Instantiation Options
% 23.78/3.50  
% 23.78/3.50  --instantiation_flag                    true
% 23.78/3.50  --inst_sos_flag                         true
% 23.78/3.50  --inst_sos_phase                        true
% 23.78/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.78/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.78/3.50  --inst_lit_sel_side                     num_symb
% 23.78/3.50  --inst_solver_per_active                1400
% 23.78/3.50  --inst_solver_calls_frac                1.
% 23.78/3.50  --inst_passive_queue_type               priority_queues
% 23.78/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.78/3.50  --inst_passive_queues_freq              [25;2]
% 23.78/3.50  --inst_dismatching                      true
% 23.78/3.50  --inst_eager_unprocessed_to_passive     true
% 23.78/3.50  --inst_prop_sim_given                   true
% 23.78/3.50  --inst_prop_sim_new                     false
% 23.78/3.50  --inst_subs_new                         false
% 23.78/3.50  --inst_eq_res_simp                      false
% 23.78/3.50  --inst_subs_given                       false
% 23.78/3.50  --inst_orphan_elimination               true
% 23.78/3.50  --inst_learning_loop_flag               true
% 23.78/3.50  --inst_learning_start                   3000
% 23.78/3.50  --inst_learning_factor                  2
% 23.78/3.50  --inst_start_prop_sim_after_learn       3
% 23.78/3.50  --inst_sel_renew                        solver
% 23.78/3.50  --inst_lit_activity_flag                true
% 23.78/3.50  --inst_restr_to_given                   false
% 23.78/3.50  --inst_activity_threshold               500
% 23.78/3.50  --inst_out_proof                        true
% 23.78/3.50  
% 23.78/3.50  ------ Resolution Options
% 23.78/3.50  
% 23.78/3.50  --resolution_flag                       true
% 23.78/3.50  --res_lit_sel                           adaptive
% 23.78/3.50  --res_lit_sel_side                      none
% 23.78/3.50  --res_ordering                          kbo
% 23.78/3.50  --res_to_prop_solver                    active
% 23.78/3.50  --res_prop_simpl_new                    false
% 23.78/3.50  --res_prop_simpl_given                  true
% 23.78/3.50  --res_passive_queue_type                priority_queues
% 23.78/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.78/3.50  --res_passive_queues_freq               [15;5]
% 23.78/3.50  --res_forward_subs                      full
% 23.78/3.50  --res_backward_subs                     full
% 23.78/3.50  --res_forward_subs_resolution           true
% 23.78/3.50  --res_backward_subs_resolution          true
% 23.78/3.50  --res_orphan_elimination                true
% 23.78/3.50  --res_time_limit                        2.
% 23.78/3.50  --res_out_proof                         true
% 23.78/3.50  
% 23.78/3.50  ------ Superposition Options
% 23.78/3.50  
% 23.78/3.50  --superposition_flag                    true
% 23.78/3.50  --sup_passive_queue_type                priority_queues
% 23.78/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.78/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.78/3.50  --demod_completeness_check              fast
% 23.78/3.50  --demod_use_ground                      true
% 23.78/3.50  --sup_to_prop_solver                    passive
% 23.78/3.50  --sup_prop_simpl_new                    true
% 23.78/3.50  --sup_prop_simpl_given                  true
% 23.78/3.50  --sup_fun_splitting                     true
% 23.78/3.50  --sup_smt_interval                      50000
% 23.78/3.50  
% 23.78/3.50  ------ Superposition Simplification Setup
% 23.78/3.50  
% 23.78/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.78/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.78/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.78/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.78/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.78/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.78/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.78/3.50  --sup_immed_triv                        [TrivRules]
% 23.78/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.78/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.78/3.50  --sup_immed_bw_main                     []
% 23.78/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.78/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.78/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.78/3.50  --sup_input_bw                          []
% 23.78/3.50  
% 23.78/3.50  ------ Combination Options
% 23.78/3.50  
% 23.78/3.50  --comb_res_mult                         3
% 23.78/3.50  --comb_sup_mult                         2
% 23.78/3.50  --comb_inst_mult                        10
% 23.78/3.50  
% 23.78/3.50  ------ Debug Options
% 23.78/3.50  
% 23.78/3.50  --dbg_backtrace                         false
% 23.78/3.50  --dbg_dump_prop_clauses                 false
% 23.78/3.50  --dbg_dump_prop_clauses_file            -
% 23.78/3.50  --dbg_out_stat                          false
% 23.78/3.50  ------ Parsing...
% 23.78/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  ------ Proving...
% 23.78/3.50  ------ Problem Properties 
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  clauses                                 9
% 23.78/3.50  conjectures                             1
% 23.78/3.50  EPR                                     0
% 23.78/3.50  Horn                                    9
% 23.78/3.50  unary                                   9
% 23.78/3.50  binary                                  0
% 23.78/3.50  lits                                    9
% 23.78/3.50  lits eq                                 9
% 23.78/3.50  fd_pure                                 0
% 23.78/3.50  fd_pseudo                               0
% 23.78/3.50  fd_cond                                 0
% 23.78/3.50  fd_pseudo_cond                          0
% 23.78/3.50  AC symbols                              0
% 23.78/3.50  
% 23.78/3.50  ------ Schedule UEQ
% 23.78/3.50  
% 23.78/3.50  ------ pure equality problem: resolution off 
% 23.78/3.50  
% 23.78/3.50  ------ Option_UEQ Time Limit: Unbounded
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ 
% 23.78/3.50  Current options:
% 23.78/3.50  ------ 
% 23.78/3.50  
% 23.78/3.50  ------ Input Options
% 23.78/3.50  
% 23.78/3.50  --out_options                           all
% 23.78/3.50  --tptp_safe_out                         true
% 23.78/3.50  --problem_path                          ""
% 23.78/3.50  --include_path                          ""
% 23.78/3.50  --clausifier                            res/vclausify_rel
% 23.78/3.50  --clausifier_options                    ""
% 23.78/3.50  --stdin                                 false
% 23.78/3.50  --stats_out                             all
% 23.78/3.50  
% 23.78/3.50  ------ General Options
% 23.78/3.50  
% 23.78/3.50  --fof                                   false
% 23.78/3.50  --time_out_real                         305.
% 23.78/3.50  --time_out_virtual                      -1.
% 23.78/3.50  --symbol_type_check                     false
% 23.78/3.50  --clausify_out                          false
% 23.78/3.50  --sig_cnt_out                           false
% 23.78/3.50  --trig_cnt_out                          false
% 23.78/3.50  --trig_cnt_out_tolerance                1.
% 23.78/3.50  --trig_cnt_out_sk_spl                   false
% 23.78/3.50  --abstr_cl_out                          false
% 23.78/3.50  
% 23.78/3.50  ------ Global Options
% 23.78/3.50  
% 23.78/3.50  --schedule                              default
% 23.78/3.50  --add_important_lit                     false
% 23.78/3.50  --prop_solver_per_cl                    1000
% 23.78/3.50  --min_unsat_core                        false
% 23.78/3.50  --soft_assumptions                      false
% 23.78/3.50  --soft_lemma_size                       3
% 23.78/3.50  --prop_impl_unit_size                   0
% 23.78/3.50  --prop_impl_unit                        []
% 23.78/3.50  --share_sel_clauses                     true
% 23.78/3.50  --reset_solvers                         false
% 23.78/3.50  --bc_imp_inh                            [conj_cone]
% 23.78/3.50  --conj_cone_tolerance                   3.
% 23.78/3.50  --extra_neg_conj                        none
% 23.78/3.50  --large_theory_mode                     true
% 23.78/3.50  --prolific_symb_bound                   200
% 23.78/3.50  --lt_threshold                          2000
% 23.78/3.50  --clause_weak_htbl                      true
% 23.78/3.50  --gc_record_bc_elim                     false
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing Options
% 23.78/3.50  
% 23.78/3.50  --preprocessing_flag                    true
% 23.78/3.50  --time_out_prep_mult                    0.1
% 23.78/3.50  --splitting_mode                        input
% 23.78/3.50  --splitting_grd                         true
% 23.78/3.50  --splitting_cvd                         false
% 23.78/3.50  --splitting_cvd_svl                     false
% 23.78/3.50  --splitting_nvd                         32
% 23.78/3.50  --sub_typing                            true
% 23.78/3.50  --prep_gs_sim                           true
% 23.78/3.50  --prep_unflatten                        true
% 23.78/3.50  --prep_res_sim                          true
% 23.78/3.50  --prep_upred                            true
% 23.78/3.50  --prep_sem_filter                       exhaustive
% 23.78/3.50  --prep_sem_filter_out                   false
% 23.78/3.50  --pred_elim                             true
% 23.78/3.50  --res_sim_input                         true
% 23.78/3.50  --eq_ax_congr_red                       true
% 23.78/3.50  --pure_diseq_elim                       true
% 23.78/3.50  --brand_transform                       false
% 23.78/3.50  --non_eq_to_eq                          false
% 23.78/3.50  --prep_def_merge                        true
% 23.78/3.50  --prep_def_merge_prop_impl              false
% 23.78/3.50  --prep_def_merge_mbd                    true
% 23.78/3.50  --prep_def_merge_tr_red                 false
% 23.78/3.50  --prep_def_merge_tr_cl                  false
% 23.78/3.50  --smt_preprocessing                     true
% 23.78/3.50  --smt_ac_axioms                         fast
% 23.78/3.50  --preprocessed_out                      false
% 23.78/3.50  --preprocessed_stats                    false
% 23.78/3.50  
% 23.78/3.50  ------ Abstraction refinement Options
% 23.78/3.50  
% 23.78/3.50  --abstr_ref                             []
% 23.78/3.50  --abstr_ref_prep                        false
% 23.78/3.50  --abstr_ref_until_sat                   false
% 23.78/3.50  --abstr_ref_sig_restrict                funpre
% 23.78/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.78/3.50  --abstr_ref_under                       []
% 23.78/3.50  
% 23.78/3.50  ------ SAT Options
% 23.78/3.50  
% 23.78/3.50  --sat_mode                              false
% 23.78/3.50  --sat_fm_restart_options                ""
% 23.78/3.50  --sat_gr_def                            false
% 23.78/3.50  --sat_epr_types                         true
% 23.78/3.50  --sat_non_cyclic_types                  false
% 23.78/3.50  --sat_finite_models                     false
% 23.78/3.50  --sat_fm_lemmas                         false
% 23.78/3.50  --sat_fm_prep                           false
% 23.78/3.50  --sat_fm_uc_incr                        true
% 23.78/3.50  --sat_out_model                         small
% 23.78/3.50  --sat_out_clauses                       false
% 23.78/3.50  
% 23.78/3.50  ------ QBF Options
% 23.78/3.50  
% 23.78/3.50  --qbf_mode                              false
% 23.78/3.50  --qbf_elim_univ                         false
% 23.78/3.50  --qbf_dom_inst                          none
% 23.78/3.50  --qbf_dom_pre_inst                      false
% 23.78/3.50  --qbf_sk_in                             false
% 23.78/3.50  --qbf_pred_elim                         true
% 23.78/3.50  --qbf_split                             512
% 23.78/3.50  
% 23.78/3.50  ------ BMC1 Options
% 23.78/3.50  
% 23.78/3.50  --bmc1_incremental                      false
% 23.78/3.50  --bmc1_axioms                           reachable_all
% 23.78/3.50  --bmc1_min_bound                        0
% 23.78/3.50  --bmc1_max_bound                        -1
% 23.78/3.50  --bmc1_max_bound_default                -1
% 23.78/3.50  --bmc1_symbol_reachability              true
% 23.78/3.50  --bmc1_property_lemmas                  false
% 23.78/3.50  --bmc1_k_induction                      false
% 23.78/3.50  --bmc1_non_equiv_states                 false
% 23.78/3.50  --bmc1_deadlock                         false
% 23.78/3.50  --bmc1_ucm                              false
% 23.78/3.50  --bmc1_add_unsat_core                   none
% 23.78/3.50  --bmc1_unsat_core_children              false
% 23.78/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.78/3.50  --bmc1_out_stat                         full
% 23.78/3.50  --bmc1_ground_init                      false
% 23.78/3.50  --bmc1_pre_inst_next_state              false
% 23.78/3.50  --bmc1_pre_inst_state                   false
% 23.78/3.50  --bmc1_pre_inst_reach_state             false
% 23.78/3.50  --bmc1_out_unsat_core                   false
% 23.78/3.50  --bmc1_aig_witness_out                  false
% 23.78/3.50  --bmc1_verbose                          false
% 23.78/3.50  --bmc1_dump_clauses_tptp                false
% 23.78/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.78/3.50  --bmc1_dump_file                        -
% 23.78/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.78/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.78/3.50  --bmc1_ucm_extend_mode                  1
% 23.78/3.50  --bmc1_ucm_init_mode                    2
% 23.78/3.50  --bmc1_ucm_cone_mode                    none
% 23.78/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.78/3.50  --bmc1_ucm_relax_model                  4
% 23.78/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.78/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.78/3.50  --bmc1_ucm_layered_model                none
% 23.78/3.50  --bmc1_ucm_max_lemma_size               10
% 23.78/3.50  
% 23.78/3.50  ------ AIG Options
% 23.78/3.50  
% 23.78/3.50  --aig_mode                              false
% 23.78/3.50  
% 23.78/3.50  ------ Instantiation Options
% 23.78/3.50  
% 23.78/3.50  --instantiation_flag                    false
% 23.78/3.50  --inst_sos_flag                         true
% 23.78/3.50  --inst_sos_phase                        true
% 23.78/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.78/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.78/3.50  --inst_lit_sel_side                     num_symb
% 23.78/3.50  --inst_solver_per_active                1400
% 23.78/3.50  --inst_solver_calls_frac                1.
% 23.78/3.50  --inst_passive_queue_type               priority_queues
% 23.78/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.78/3.50  --inst_passive_queues_freq              [25;2]
% 23.78/3.50  --inst_dismatching                      true
% 23.78/3.50  --inst_eager_unprocessed_to_passive     true
% 23.78/3.50  --inst_prop_sim_given                   true
% 23.78/3.50  --inst_prop_sim_new                     false
% 23.78/3.50  --inst_subs_new                         false
% 23.78/3.50  --inst_eq_res_simp                      false
% 23.78/3.50  --inst_subs_given                       false
% 23.78/3.50  --inst_orphan_elimination               true
% 23.78/3.50  --inst_learning_loop_flag               true
% 23.78/3.50  --inst_learning_start                   3000
% 23.78/3.50  --inst_learning_factor                  2
% 23.78/3.50  --inst_start_prop_sim_after_learn       3
% 23.78/3.50  --inst_sel_renew                        solver
% 23.78/3.50  --inst_lit_activity_flag                true
% 23.78/3.50  --inst_restr_to_given                   false
% 23.78/3.50  --inst_activity_threshold               500
% 23.78/3.50  --inst_out_proof                        true
% 23.78/3.50  
% 23.78/3.50  ------ Resolution Options
% 23.78/3.50  
% 23.78/3.50  --resolution_flag                       false
% 23.78/3.50  --res_lit_sel                           adaptive
% 23.78/3.50  --res_lit_sel_side                      none
% 23.78/3.50  --res_ordering                          kbo
% 23.78/3.50  --res_to_prop_solver                    active
% 23.78/3.50  --res_prop_simpl_new                    false
% 23.78/3.50  --res_prop_simpl_given                  true
% 23.78/3.50  --res_passive_queue_type                priority_queues
% 23.78/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.78/3.50  --res_passive_queues_freq               [15;5]
% 23.78/3.50  --res_forward_subs                      full
% 23.78/3.50  --res_backward_subs                     full
% 23.78/3.50  --res_forward_subs_resolution           true
% 23.78/3.50  --res_backward_subs_resolution          true
% 23.78/3.50  --res_orphan_elimination                true
% 23.78/3.50  --res_time_limit                        2.
% 23.78/3.50  --res_out_proof                         true
% 23.78/3.50  
% 23.78/3.50  ------ Superposition Options
% 23.78/3.50  
% 23.78/3.50  --superposition_flag                    true
% 23.78/3.50  --sup_passive_queue_type                priority_queues
% 23.78/3.50  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.78/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.78/3.50  --demod_completeness_check              fast
% 23.78/3.50  --demod_use_ground                      true
% 23.78/3.50  --sup_to_prop_solver                    active
% 23.78/3.50  --sup_prop_simpl_new                    false
% 23.78/3.50  --sup_prop_simpl_given                  false
% 23.78/3.50  --sup_fun_splitting                     true
% 23.78/3.50  --sup_smt_interval                      10000
% 23.78/3.50  
% 23.78/3.50  ------ Superposition Simplification Setup
% 23.78/3.50  
% 23.78/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.78/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.78/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.78/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.78/3.50  --sup_full_triv                         [TrivRules]
% 23.78/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.78/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.78/3.50  --sup_immed_triv                        [TrivRules]
% 23.78/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.78/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.78/3.50  --sup_immed_bw_main                     []
% 23.78/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.78/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.78/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.78/3.50  --sup_input_bw                          [BwDemod;BwSubsumption]
% 23.78/3.50  
% 23.78/3.50  ------ Combination Options
% 23.78/3.50  
% 23.78/3.50  --comb_res_mult                         1
% 23.78/3.50  --comb_sup_mult                         1
% 23.78/3.50  --comb_inst_mult                        1000000
% 23.78/3.50  
% 23.78/3.50  ------ Debug Options
% 23.78/3.50  
% 23.78/3.50  --dbg_backtrace                         false
% 23.78/3.50  --dbg_dump_prop_clauses                 false
% 23.78/3.50  --dbg_dump_prop_clauses_file            -
% 23.78/3.50  --dbg_out_stat                          false
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  % SZS status Theorem for theBenchmark.p
% 23.78/3.50  
% 23.78/3.50   Resolution empty clause
% 23.78/3.50  
% 23.78/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.78/3.50  
% 23.78/3.50  fof(f8,axiom,(
% 23.78/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f27,plain,(
% 23.78/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f8])).
% 23.78/3.50  
% 23.78/3.50  fof(f9,axiom,(
% 23.78/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f28,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f9])).
% 23.78/3.50  
% 23.78/3.50  fof(f10,axiom,(
% 23.78/3.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f29,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f10])).
% 23.78/3.50  
% 23.78/3.50  fof(f11,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f30,plain,(
% 23.78/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f11])).
% 23.78/3.50  
% 23.78/3.50  fof(f35,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f29,f30])).
% 23.78/3.50  
% 23.78/3.50  fof(f36,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f28,f35])).
% 23.78/3.50  
% 23.78/3.50  fof(f40,plain,(
% 23.78/3.50    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f27,f36])).
% 23.78/3.50  
% 23.78/3.50  fof(f5,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f24,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 23.78/3.50    inference(cnf_transformation,[],[f5])).
% 23.78/3.50  
% 23.78/3.50  fof(f45,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k1_tarski(X4))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f24,f30])).
% 23.78/3.50  
% 23.78/3.50  fof(f4,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f23,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 23.78/3.50    inference(cnf_transformation,[],[f4])).
% 23.78/3.50  
% 23.78/3.50  fof(f41,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f23,f30])).
% 23.78/3.50  
% 23.78/3.50  fof(f1,axiom,(
% 23.78/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f20,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f1])).
% 23.78/3.50  
% 23.78/3.50  fof(f42,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f20,f36,f36])).
% 23.78/3.50  
% 23.78/3.50  fof(f7,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f26,plain,(
% 23.78/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f7])).
% 23.78/3.50  
% 23.78/3.50  fof(f6,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f25,plain,(
% 23.78/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f6])).
% 23.78/3.50  
% 23.78/3.50  fof(f37,plain,(
% 23.78/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f25,f35])).
% 23.78/3.50  
% 23.78/3.50  fof(f46,plain,(
% 23.78/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f26,f35,f37])).
% 23.78/3.50  
% 23.78/3.50  fof(f12,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f31,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f12])).
% 23.78/3.50  
% 23.78/3.50  fof(f13,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f32,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f13])).
% 23.78/3.50  
% 23.78/3.50  fof(f14,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f33,plain,(
% 23.78/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f14])).
% 23.78/3.50  
% 23.78/3.50  fof(f38,plain,(
% 23.78/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f33,f37])).
% 23.78/3.50  
% 23.78/3.50  fof(f39,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f32,f38])).
% 23.78/3.50  
% 23.78/3.50  fof(f47,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f31,f39])).
% 23.78/3.50  
% 23.78/3.50  fof(f3,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f22,plain,(
% 23.78/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f3])).
% 23.78/3.50  
% 23.78/3.50  fof(f44,plain,(
% 23.78/3.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f22,f30,f30])).
% 23.78/3.50  
% 23.78/3.50  fof(f2,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f21,plain,(
% 23.78/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f2])).
% 23.78/3.50  
% 23.78/3.50  fof(f43,plain,(
% 23.78/3.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X3,X2)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f21,f30,f30])).
% 23.78/3.50  
% 23.78/3.50  fof(f15,conjecture,(
% 23.78/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f16,negated_conjecture,(
% 23.78/3.50    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 23.78/3.50    inference(negated_conjecture,[],[f15])).
% 23.78/3.50  
% 23.78/3.50  fof(f17,plain,(
% 23.78/3.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 23.78/3.50    inference(ennf_transformation,[],[f16])).
% 23.78/3.50  
% 23.78/3.50  fof(f18,plain,(
% 23.78/3.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 23.78/3.50    introduced(choice_axiom,[])).
% 23.78/3.50  
% 23.78/3.50  fof(f19,plain,(
% 23.78/3.50    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 23.78/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).
% 23.78/3.50  
% 23.78/3.50  fof(f34,plain,(
% 23.78/3.50    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 23.78/3.50    inference(cnf_transformation,[],[f19])).
% 23.78/3.50  
% 23.78/3.50  fof(f48,plain,(
% 23.78/3.50    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3)),
% 23.78/3.50    inference(definition_unfolding,[],[f34,f30,f30])).
% 23.78/3.50  
% 23.78/3.50  cnf(c_0,plain,
% 23.78/3.50      ( k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
% 23.78/3.50      inference(cnf_transformation,[],[f40]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_27,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36) = k1_tarski(X0_36) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_0]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_5,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 23.78/3.50      inference(cnf_transformation,[],[f45]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_22,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k1_tarski(X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_5]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_216,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_27,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 23.78/3.50      inference(cnf_transformation,[],[f41]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_26,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_1]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_267,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X1_36,X1_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_216,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2,plain,
% 23.78/3.50      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 23.78/3.50      inference(cnf_transformation,[],[f42]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_25,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_2]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_238,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X2_36)) = k3_enumset1(X0_36,X2_36,X2_36,X2_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_25,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_243,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X2_36,X2_36,X2_36,X1_36) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_238,c_26,c_216]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_588,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X2_36) = k3_enumset1(X0_36,X2_36,X2_36,X2_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_267,c_243]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_244,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_216,c_25]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_6,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7)) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
% 23.78/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_21,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X5_36,X6_36,X7_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_6]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_304,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_244,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_320,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X1_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_304,c_244]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_255,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)) = k1_tarski(X0_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_216,c_27]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_256,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_216,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_271,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_256,c_216]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_272,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_255,c_271]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_7,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 23.78/3.50      inference(cnf_transformation,[],[f47]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_20,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_7]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_39,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_20,c_27]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_273,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_272,c_39]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_321,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_320,c_273]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_322,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_321,c_39,c_255]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_734,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X2_36) = k3_enumset1(X1_36,X2_36,X2_36,X2_36,X0_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_588,c_322]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_4,plain,
% 23.78/3.50      ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X1,X2) ),
% 23.78/3.50      inference(cnf_transformation,[],[f44]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_23,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X3_36,X1_36,X2_36) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_4]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_265,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_216,c_23]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_344,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_265,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1150,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) = k3_enumset1(X0_36,X1_36,X1_36,X1_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_344,c_267]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1623,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) = k3_enumset1(X2_36,X0_36,X2_36,X2_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_734,c_1150]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_163,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k3_enumset1(X2_36,X3_36,X4_36,X5_36,X6_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36),k3_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_23,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_952,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k3_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X3_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X2_36,X4_36,X5_36,X6_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_163,c_244]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_4988,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X0_36,X1_36),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X1_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1623,c_952]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_41,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_23,c_23]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_732,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X0_36) = k3_enumset1(X0_36,X0_36,X1_36,X0_36,X0_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_588,c_41]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_317,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_244,c_41]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_737,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_732,c_317]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_791,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_737,c_322]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_268,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_216,c_41]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_364,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X1_36,X0_36,X0_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_268,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_337,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_265,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1233,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X2_36) = k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_364,c_337]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_730,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_588,c_216]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_764,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X0_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_730,c_322]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2416,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1233,c_764]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_3,plain,
% 23.78/3.50      ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X3,X2) ),
% 23.78/3.50      inference(cnf_transformation,[],[f43]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_24,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X3_36,X2_36) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_3]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_50,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X2_36,X1_36,X3_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_24,c_23]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2540,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2416,c_50]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2737,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2540,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2767,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_2737,c_2540]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_241,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X3_36,X4_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_41,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2768,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X3_36,X4_36,X2_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_2767,c_241,c_255]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_5084,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X3_36,X4_36,X2_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_4988,c_791,c_2768]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2415,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1233,c_791]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2476,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X1_36,X0_36,X1_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2415,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_4374,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2476,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_313,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_244,c_23]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_260,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_216,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_535,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_260,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_564,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_535,c_27]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_4448,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X0_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X1_36),k3_enumset1(X0_36,X2_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_4374,c_313,c_564]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_5085,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X0_36,X1_36,X4_36,X2_36,X3_36) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_5084,c_39,c_255,c_4448]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_176,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X6_36,X7_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_23,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_10661,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_27,c_176]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_448,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_41,c_39]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_11511,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X1_36)) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_10661,c_27,c_448]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_102704,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X1_36) = k3_enumset1(X0_36,X0_36,X2_36,X3_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_11511,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_180,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X6_36,X5_36,X7_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_50,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_23169,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2540,c_180]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_222,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k1_tarski(X4_36)) = k3_enumset1(X0_36,X3_36,X1_36,X2_36,X4_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_23,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_17136,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X0_36,X3_36,X1_36,X2_36,X4_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_222,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_370,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X2_36,X1_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_268,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1315,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X2_36,X1_36,X1_36) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_370,c_344]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1672,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1150,c_737]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_3632,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1315,c_1672]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_17660,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_17136,c_3632]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_23261,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_17660,c_180]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_23853,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X0_36,X0_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_23261,c_244]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2484,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2415,c_50]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2642,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2484,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_177,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X3_36,X4_36,X5_36,X6_36,X7_36)) = k2_xboole_0(k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36),k3_enumset1(X5_36,X5_36,X5_36,X7_36,X6_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_24,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_15940,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X2_36,X2_36,X3_36,X5_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2642,c_177]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2485,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2415,c_41]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2697,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X1_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2485,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_15944,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X2_36,X1_36,X3_36,X5_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2697,c_177]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2541,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X0_36) = k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2416,c_41]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2806,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))) = k3_enumset1(X0_36,X2_36,X1_36,X1_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2541,c_26]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_15948,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X2_36,X1_36),k3_enumset1(X1_36,X2_36,X3_36,X5_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2806,c_177]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_6598,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2642,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_6673,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_6598,c_2540]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_2636,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)) = k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2484,c_22]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_6434,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k1_tarski(X2_36)),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X2_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X1_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_2636,c_952]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_6511,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X1_36),k3_enumset1(X2_36,X0_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_6434,c_564]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_6674,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X2_36,X1_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_6673,c_6511]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_16109,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k3_enumset1(X2_36,X1_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X5_36,X4_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_15948,c_6674]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_16116,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k2_xboole_0(k1_tarski(X1_36),k1_tarski(X2_36))),k3_enumset1(X3_36,X3_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X4_36,X5_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_15944,c_16109]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_16119,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X2_36,X3_36,X5_36,X4_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_15940,c_16116]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_16120,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36)) = k2_xboole_0(k1_tarski(X1_36),k3_enumset1(X0_36,X2_36,X3_36,X5_36,X4_36)) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_16119,c_2540]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1673,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X1_36,X0_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1150,c_730]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_3631,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X0_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1315,c_1673]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_17661,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X1_36) = k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_17136,c_3631]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_18338,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_17661,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_15918,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X4_36,X3_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1672,c_177]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1709,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_1672,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_386,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_313,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_402,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1_36),k1_tarski(X0_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_386,c_313]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_333,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_265,c_21]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_348,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X0_36)),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_333,c_265]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_349,plain,
% 23.78/3.50      ( k2_xboole_0(k1_tarski(X0_36),k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_348,c_255,c_273]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_403,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_402,c_255,c_349]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1727,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36),k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_1709,c_403]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_16158,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X4_36,X3_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_15918,c_1727]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_18390,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X0_36,X0_36,X2_36,X3_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X4_36,X3_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_18338,c_244,c_16158]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_23854,plain,
% 23.78/3.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_36),k1_tarski(X1_36)),k3_enumset1(X2_36,X2_36,X3_36,X2_36,X4_36)) = k3_enumset1(X0_36,X1_36,X2_36,X4_36,X3_36) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_23853,c_16120,c_18390]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_23998,plain,
% 23.78/3.50      ( k2_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36),k3_enumset1(X1_36,X1_36,X2_36,X3_36,X4_36)) = k3_enumset1(X1_36,X0_36,X2_36,X4_36,X3_36) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_23169,c_23854]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_23999,plain,
% 23.78/3.50      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X1_36,X0_36,X4_36,X3_36,X2_36) ),
% 23.78/3.50      inference(light_normalisation,[status(thm)],[c_23998,c_27,c_241]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_8,negated_conjecture,
% 23.78/3.50      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 23.78/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_19,negated_conjecture,
% 23.78/3.50      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 23.78/3.50      inference(subtyping,[status(esa)],[c_8]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_17144,plain,
% 23.78/3.50      ( k3_enumset1(sK1,sK0,sK2,sK1,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_17136,c_19]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_24646,plain,
% 23.78/3.50      ( k3_enumset1(sK0,sK1,sK3,sK1,sK2) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_23999,c_17144]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_73146,plain,
% 23.78/3.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK1) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_5085,c_24646]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_103220,plain,
% 23.78/3.50      ( k3_enumset1(sK0,sK0,sK2,sK3,sK1) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_102704,c_73146]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_105682,plain,
% 23.78/3.50      ( $false ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_5085,c_103220]) ).
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.78/3.50  
% 23.78/3.50  ------                               Statistics
% 23.78/3.50  
% 23.78/3.50  ------ General
% 23.78/3.50  
% 23.78/3.50  abstr_ref_over_cycles:                  0
% 23.78/3.50  abstr_ref_under_cycles:                 0
% 23.78/3.50  gc_basic_clause_elim:                   0
% 23.78/3.50  forced_gc_time:                         0
% 23.78/3.50  parsing_time:                           0.008
% 23.78/3.50  unif_index_cands_time:                  0.
% 23.78/3.50  unif_index_add_time:                    0.
% 23.78/3.50  orderings_time:                         0.
% 23.78/3.50  out_proof_time:                         0.028
% 23.78/3.50  total_time:                             2.905
% 23.78/3.50  num_of_symbols:                         40
% 23.78/3.50  num_of_terms:                           56243
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing
% 23.78/3.50  
% 23.78/3.50  num_of_splits:                          0
% 23.78/3.50  num_of_split_atoms:                     0
% 23.78/3.50  num_of_reused_defs:                     0
% 23.78/3.50  num_eq_ax_congr_red:                    7
% 23.78/3.50  num_of_sem_filtered_clauses:            0
% 23.78/3.50  num_of_subtypes:                        2
% 23.78/3.50  monotx_restored_types:                  0
% 23.78/3.50  sat_num_of_epr_types:                   0
% 23.78/3.50  sat_num_of_non_cyclic_types:            0
% 23.78/3.50  sat_guarded_non_collapsed_types:        0
% 23.78/3.50  num_pure_diseq_elim:                    0
% 23.78/3.50  simp_replaced_by:                       0
% 23.78/3.50  res_preprocessed:                       21
% 23.78/3.50  prep_upred:                             0
% 23.78/3.50  prep_unflattend:                        0
% 23.78/3.50  smt_new_axioms:                         0
% 23.78/3.50  pred_elim_cands:                        0
% 23.78/3.50  pred_elim:                              0
% 23.78/3.50  pred_elim_cl:                           0
% 23.78/3.50  pred_elim_cycles:                       0
% 23.78/3.50  merged_defs:                            0
% 23.78/3.50  merged_defs_ncl:                        0
% 23.78/3.50  bin_hyper_res:                          0
% 23.78/3.50  prep_cycles:                            2
% 23.78/3.50  pred_elim_time:                         0.
% 23.78/3.50  splitting_time:                         0.
% 23.78/3.50  sem_filter_time:                        0.
% 23.78/3.50  monotx_time:                            0.
% 23.78/3.50  subtype_inf_time:                       0.
% 23.78/3.50  
% 23.78/3.50  ------ Problem properties
% 23.78/3.50  
% 23.78/3.50  clauses:                                9
% 23.78/3.50  conjectures:                            1
% 23.78/3.50  epr:                                    0
% 23.78/3.50  horn:                                   9
% 23.78/3.50  ground:                                 1
% 23.78/3.50  unary:                                  9
% 23.78/3.50  binary:                                 0
% 23.78/3.50  lits:                                   9
% 23.78/3.50  lits_eq:                                9
% 23.78/3.50  fd_pure:                                0
% 23.78/3.50  fd_pseudo:                              0
% 23.78/3.50  fd_cond:                                0
% 23.78/3.50  fd_pseudo_cond:                         0
% 23.78/3.50  ac_symbols:                             0
% 23.78/3.50  
% 23.78/3.50  ------ Propositional Solver
% 23.78/3.50  
% 23.78/3.50  prop_solver_calls:                      13
% 23.78/3.50  prop_fast_solver_calls:                 50
% 23.78/3.50  smt_solver_calls:                       0
% 23.78/3.50  smt_fast_solver_calls:                  0
% 23.78/3.50  prop_num_of_clauses:                    314
% 23.78/3.50  prop_preprocess_simplified:             530
% 23.78/3.50  prop_fo_subsumed:                       0
% 23.78/3.50  prop_solver_time:                       0.
% 23.78/3.50  smt_solver_time:                        0.
% 23.78/3.50  smt_fast_solver_time:                   0.
% 23.78/3.50  prop_fast_solver_time:                  0.
% 23.78/3.50  prop_unsat_core_time:                   0.
% 23.78/3.50  
% 23.78/3.50  ------ QBF
% 23.78/3.50  
% 23.78/3.50  qbf_q_res:                              0
% 23.78/3.50  qbf_num_tautologies:                    0
% 23.78/3.50  qbf_prep_cycles:                        0
% 23.78/3.50  
% 23.78/3.50  ------ BMC1
% 23.78/3.50  
% 23.78/3.50  bmc1_current_bound:                     -1
% 23.78/3.50  bmc1_last_solved_bound:                 -1
% 23.78/3.50  bmc1_unsat_core_size:                   -1
% 23.78/3.50  bmc1_unsat_core_parents_size:           -1
% 23.78/3.50  bmc1_merge_next_fun:                    0
% 23.78/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.78/3.50  
% 23.78/3.50  ------ Instantiation
% 23.78/3.50  
% 23.78/3.50  inst_num_of_clauses:                    0
% 23.78/3.50  inst_num_in_passive:                    0
% 23.78/3.50  inst_num_in_active:                     0
% 23.78/3.50  inst_num_in_unprocessed:                0
% 23.78/3.50  inst_num_of_loops:                      0
% 23.78/3.50  inst_num_of_learning_restarts:          0
% 23.78/3.50  inst_num_moves_active_passive:          0
% 23.78/3.50  inst_lit_activity:                      0
% 23.78/3.50  inst_lit_activity_moves:                0
% 23.78/3.50  inst_num_tautologies:                   0
% 23.78/3.50  inst_num_prop_implied:                  0
% 23.78/3.50  inst_num_existing_simplified:           0
% 23.78/3.50  inst_num_eq_res_simplified:             0
% 23.78/3.50  inst_num_child_elim:                    0
% 23.78/3.50  inst_num_of_dismatching_blockings:      0
% 23.78/3.50  inst_num_of_non_proper_insts:           0
% 23.78/3.50  inst_num_of_duplicates:                 0
% 23.78/3.50  inst_inst_num_from_inst_to_res:         0
% 23.78/3.50  inst_dismatching_checking_time:         0.
% 23.78/3.50  
% 23.78/3.50  ------ Resolution
% 23.78/3.50  
% 23.78/3.50  res_num_of_clauses:                     0
% 23.78/3.50  res_num_in_passive:                     0
% 23.78/3.50  res_num_in_active:                      0
% 23.78/3.50  res_num_of_loops:                       23
% 23.78/3.50  res_forward_subset_subsumed:            0
% 23.78/3.50  res_backward_subset_subsumed:           0
% 23.78/3.50  res_forward_subsumed:                   0
% 23.78/3.50  res_backward_subsumed:                  0
% 23.78/3.50  res_forward_subsumption_resolution:     0
% 23.78/3.50  res_backward_subsumption_resolution:    0
% 23.78/3.50  res_clause_to_clause_subsumption:       388474
% 23.78/3.50  res_orphan_elimination:                 0
% 23.78/3.50  res_tautology_del:                      0
% 23.78/3.50  res_num_eq_res_simplified:              0
% 23.78/3.50  res_num_sel_changes:                    0
% 23.78/3.50  res_moves_from_active_to_pass:          0
% 23.78/3.50  
% 23.78/3.50  ------ Superposition
% 23.78/3.50  
% 23.78/3.50  sup_time_total:                         0.
% 23.78/3.50  sup_time_generating:                    0.
% 23.78/3.50  sup_time_sim_full:                      0.
% 23.78/3.50  sup_time_sim_immed:                     0.
% 23.78/3.50  
% 23.78/3.50  sup_num_of_clauses:                     5663
% 23.78/3.50  sup_num_in_active:                      253
% 23.78/3.50  sup_num_in_passive:                     5410
% 23.78/3.50  sup_num_of_loops:                       277
% 23.78/3.50  sup_fw_superposition:                   51316
% 23.78/3.50  sup_bw_superposition:                   43902
% 23.78/3.50  sup_immediate_simplified:               9315
% 23.78/3.50  sup_given_eliminated:                   1
% 23.78/3.50  comparisons_done:                       0
% 23.78/3.50  comparisons_avoided:                    0
% 23.78/3.50  
% 23.78/3.50  ------ Simplifications
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  sim_fw_subset_subsumed:                 0
% 23.78/3.50  sim_bw_subset_subsumed:                 0
% 23.78/3.50  sim_fw_subsumed:                        367
% 23.78/3.50  sim_bw_subsumed:                        78
% 23.78/3.50  sim_fw_subsumption_res:                 0
% 23.78/3.50  sim_bw_subsumption_res:                 0
% 23.78/3.50  sim_tautology_del:                      0
% 23.78/3.50  sim_eq_tautology_del:                   577
% 23.78/3.50  sim_eq_res_simp:                        0
% 23.78/3.50  sim_fw_demodulated:                     6030
% 23.78/3.50  sim_bw_demodulated:                     134
% 23.78/3.50  sim_light_normalised:                   4252
% 23.78/3.50  sim_joinable_taut:                      0
% 23.78/3.50  sim_joinable_simp:                      0
% 23.78/3.50  sim_ac_normalised:                      0
% 23.78/3.50  sim_smt_subsumption:                    0
% 23.78/3.50  
%------------------------------------------------------------------------------
