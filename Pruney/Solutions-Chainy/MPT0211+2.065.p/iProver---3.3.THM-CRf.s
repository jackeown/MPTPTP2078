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
% DateTime   : Thu Dec  3 11:28:33 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 611 expanded)
%              Number of clauses        :   32 (  95 expanded)
%              Number of leaves         :   13 ( 209 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 612 expanded)
%              Number of equality atoms :   70 ( 611 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f23,f32,f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f24,f32,f32])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f22,f21,f32,f37])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k2_enumset1(X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f26,f21,f39,f38])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f35,f32,f32])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f25,f21,f37,f32,f38])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f36,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f36,f21,f37,f37,f32])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,plain,
    ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X2_36,X2_36,X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,plain,
    ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X2_36,X2_36,X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_69,plain,
    ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_25,c_24])).

cnf(c_4,plain,
    ( k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X1_36,X2_36,X3_36),k4_xboole_0(k2_enumset1(X4_36,X4_36,X4_36,X4_36),k2_enumset1(X0_36,X1_36,X2_36,X3_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X4_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_269,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X1_36,X1_36,X0_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X1_36,X1_36,X0_36,X2_36))) ),
    inference(superposition,[status(thm)],[c_69,c_22])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_26,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_312,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_22,c_26])).

cnf(c_7,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,plain,
    ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X0_36,X0_36,X2_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_45,plain,
    ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X1_36,X1_36,X2_36,X0_36) ),
    inference(superposition,[status(thm)],[c_24,c_19])).

cnf(c_270,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X2_36,X2_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X2_36,X2_36,X0_36,X1_36))) ),
    inference(superposition,[status(thm)],[c_45,c_22])).

cnf(c_318,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X2_36,X0_36,X1_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_270,c_312])).

cnf(c_319,plain,
    ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X2_36,X1_36,X0_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_269,c_312,c_318])).

cnf(c_511,plain,
    ( k2_enumset1(X0_36,X1_36,X1_36,X2_36) = k2_enumset1(X0_36,X0_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_319,c_25])).

cnf(c_265,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X2_36,X1_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X2_36,X1_36))) ),
    inference(superposition,[status(thm)],[c_19,c_22])).

cnf(c_322,plain,
    ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X1_36,X0_36,X2_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_265,c_312,c_318])).

cnf(c_3,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X4_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X4_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_393,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) ),
    inference(superposition,[status(thm)],[c_23,c_22])).

cnf(c_141,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X3_36,X2_36) ),
    inference(superposition,[status(thm)],[c_45,c_26])).

cnf(c_409,plain,
    ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X1_36,X2_36,X3_36,X0_36) ),
    inference(light_normalisation,[status(thm)],[c_393,c_141,c_318])).

cnf(c_723,plain,
    ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X0_36,X3_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_322,c_409])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_40,plain,
    ( k2_enumset1(sK1,sK0,sK2,sK0) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_18,c_26])).

cnf(c_49,plain,
    ( k2_enumset1(sK1,sK1,sK2,sK0) != k2_enumset1(sK1,sK0,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_25,c_40])).

cnf(c_2467,plain,
    ( k2_enumset1(sK1,sK0,sK0,sK2) != k2_enumset1(sK1,sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_723,c_49])).

cnf(c_2695,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_511,c_2467])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:47:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.48/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.01  
% 2.48/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.01  
% 2.48/1.01  ------  iProver source info
% 2.48/1.01  
% 2.48/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.01  git: non_committed_changes: false
% 2.48/1.01  git: last_make_outside_of_git: false
% 2.48/1.01  
% 2.48/1.01  ------ 
% 2.48/1.01  
% 2.48/1.01  ------ Input Options
% 2.48/1.01  
% 2.48/1.01  --out_options                           all
% 2.48/1.01  --tptp_safe_out                         true
% 2.48/1.01  --problem_path                          ""
% 2.48/1.01  --include_path                          ""
% 2.48/1.01  --clausifier                            res/vclausify_rel
% 2.48/1.01  --clausifier_options                    --mode clausify
% 2.48/1.01  --stdin                                 false
% 2.48/1.01  --stats_out                             all
% 2.48/1.01  
% 2.48/1.01  ------ General Options
% 2.48/1.01  
% 2.48/1.01  --fof                                   false
% 2.48/1.01  --time_out_real                         305.
% 2.48/1.01  --time_out_virtual                      -1.
% 2.48/1.01  --symbol_type_check                     false
% 2.48/1.01  --clausify_out                          false
% 2.48/1.01  --sig_cnt_out                           false
% 2.48/1.01  --trig_cnt_out                          false
% 2.48/1.01  --trig_cnt_out_tolerance                1.
% 2.48/1.01  --trig_cnt_out_sk_spl                   false
% 2.48/1.01  --abstr_cl_out                          false
% 2.48/1.01  
% 2.48/1.01  ------ Global Options
% 2.48/1.01  
% 2.48/1.01  --schedule                              default
% 2.48/1.01  --add_important_lit                     false
% 2.48/1.01  --prop_solver_per_cl                    1000
% 2.48/1.01  --min_unsat_core                        false
% 2.48/1.01  --soft_assumptions                      false
% 2.48/1.01  --soft_lemma_size                       3
% 2.48/1.01  --prop_impl_unit_size                   0
% 2.48/1.01  --prop_impl_unit                        []
% 2.48/1.01  --share_sel_clauses                     true
% 2.48/1.01  --reset_solvers                         false
% 2.48/1.01  --bc_imp_inh                            [conj_cone]
% 2.48/1.01  --conj_cone_tolerance                   3.
% 2.48/1.01  --extra_neg_conj                        none
% 2.48/1.01  --large_theory_mode                     true
% 2.48/1.01  --prolific_symb_bound                   200
% 2.48/1.01  --lt_threshold                          2000
% 2.48/1.01  --clause_weak_htbl                      true
% 2.48/1.01  --gc_record_bc_elim                     false
% 2.48/1.01  
% 2.48/1.01  ------ Preprocessing Options
% 2.48/1.01  
% 2.48/1.01  --preprocessing_flag                    true
% 2.48/1.01  --time_out_prep_mult                    0.1
% 2.48/1.01  --splitting_mode                        input
% 2.48/1.01  --splitting_grd                         true
% 2.48/1.01  --splitting_cvd                         false
% 2.48/1.01  --splitting_cvd_svl                     false
% 2.48/1.01  --splitting_nvd                         32
% 2.48/1.01  --sub_typing                            true
% 2.48/1.01  --prep_gs_sim                           true
% 2.48/1.01  --prep_unflatten                        true
% 2.48/1.01  --prep_res_sim                          true
% 2.48/1.01  --prep_upred                            true
% 2.48/1.01  --prep_sem_filter                       exhaustive
% 2.48/1.01  --prep_sem_filter_out                   false
% 2.48/1.01  --pred_elim                             true
% 2.48/1.01  --res_sim_input                         true
% 2.48/1.01  --eq_ax_congr_red                       true
% 2.48/1.01  --pure_diseq_elim                       true
% 2.48/1.01  --brand_transform                       false
% 2.48/1.01  --non_eq_to_eq                          false
% 2.48/1.01  --prep_def_merge                        true
% 2.48/1.01  --prep_def_merge_prop_impl              false
% 2.48/1.01  --prep_def_merge_mbd                    true
% 2.48/1.01  --prep_def_merge_tr_red                 false
% 2.48/1.01  --prep_def_merge_tr_cl                  false
% 2.48/1.01  --smt_preprocessing                     true
% 2.48/1.01  --smt_ac_axioms                         fast
% 2.48/1.01  --preprocessed_out                      false
% 2.48/1.01  --preprocessed_stats                    false
% 2.48/1.01  
% 2.48/1.01  ------ Abstraction refinement Options
% 2.48/1.01  
% 2.48/1.01  --abstr_ref                             []
% 2.48/1.01  --abstr_ref_prep                        false
% 2.48/1.01  --abstr_ref_until_sat                   false
% 2.48/1.01  --abstr_ref_sig_restrict                funpre
% 2.48/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.01  --abstr_ref_under                       []
% 2.48/1.01  
% 2.48/1.01  ------ SAT Options
% 2.48/1.01  
% 2.48/1.01  --sat_mode                              false
% 2.48/1.01  --sat_fm_restart_options                ""
% 2.48/1.01  --sat_gr_def                            false
% 2.48/1.01  --sat_epr_types                         true
% 2.48/1.01  --sat_non_cyclic_types                  false
% 2.48/1.01  --sat_finite_models                     false
% 2.48/1.01  --sat_fm_lemmas                         false
% 2.48/1.01  --sat_fm_prep                           false
% 2.48/1.01  --sat_fm_uc_incr                        true
% 2.48/1.01  --sat_out_model                         small
% 2.48/1.01  --sat_out_clauses                       false
% 2.48/1.01  
% 2.48/1.01  ------ QBF Options
% 2.48/1.01  
% 2.48/1.01  --qbf_mode                              false
% 2.48/1.01  --qbf_elim_univ                         false
% 2.48/1.01  --qbf_dom_inst                          none
% 2.48/1.01  --qbf_dom_pre_inst                      false
% 2.48/1.01  --qbf_sk_in                             false
% 2.48/1.01  --qbf_pred_elim                         true
% 2.48/1.01  --qbf_split                             512
% 2.48/1.01  
% 2.48/1.01  ------ BMC1 Options
% 2.48/1.01  
% 2.48/1.01  --bmc1_incremental                      false
% 2.48/1.01  --bmc1_axioms                           reachable_all
% 2.48/1.01  --bmc1_min_bound                        0
% 2.48/1.01  --bmc1_max_bound                        -1
% 2.48/1.01  --bmc1_max_bound_default                -1
% 2.48/1.01  --bmc1_symbol_reachability              true
% 2.48/1.01  --bmc1_property_lemmas                  false
% 2.48/1.01  --bmc1_k_induction                      false
% 2.48/1.01  --bmc1_non_equiv_states                 false
% 2.48/1.01  --bmc1_deadlock                         false
% 2.48/1.01  --bmc1_ucm                              false
% 2.48/1.01  --bmc1_add_unsat_core                   none
% 2.48/1.01  --bmc1_unsat_core_children              false
% 2.48/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.01  --bmc1_out_stat                         full
% 2.48/1.01  --bmc1_ground_init                      false
% 2.48/1.01  --bmc1_pre_inst_next_state              false
% 2.48/1.01  --bmc1_pre_inst_state                   false
% 2.48/1.01  --bmc1_pre_inst_reach_state             false
% 2.48/1.01  --bmc1_out_unsat_core                   false
% 2.48/1.01  --bmc1_aig_witness_out                  false
% 2.48/1.01  --bmc1_verbose                          false
% 2.48/1.01  --bmc1_dump_clauses_tptp                false
% 2.48/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.01  --bmc1_dump_file                        -
% 2.48/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.01  --bmc1_ucm_extend_mode                  1
% 2.48/1.01  --bmc1_ucm_init_mode                    2
% 2.48/1.01  --bmc1_ucm_cone_mode                    none
% 2.48/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.01  --bmc1_ucm_relax_model                  4
% 2.48/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.01  --bmc1_ucm_layered_model                none
% 2.48/1.01  --bmc1_ucm_max_lemma_size               10
% 2.48/1.01  
% 2.48/1.01  ------ AIG Options
% 2.48/1.01  
% 2.48/1.01  --aig_mode                              false
% 2.48/1.01  
% 2.48/1.01  ------ Instantiation Options
% 2.48/1.01  
% 2.48/1.01  --instantiation_flag                    true
% 2.48/1.01  --inst_sos_flag                         false
% 2.48/1.01  --inst_sos_phase                        true
% 2.48/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.01  --inst_lit_sel_side                     num_symb
% 2.48/1.01  --inst_solver_per_active                1400
% 2.48/1.01  --inst_solver_calls_frac                1.
% 2.48/1.01  --inst_passive_queue_type               priority_queues
% 2.48/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.01  --inst_passive_queues_freq              [25;2]
% 2.48/1.01  --inst_dismatching                      true
% 2.48/1.01  --inst_eager_unprocessed_to_passive     true
% 2.48/1.01  --inst_prop_sim_given                   true
% 2.48/1.01  --inst_prop_sim_new                     false
% 2.48/1.01  --inst_subs_new                         false
% 2.48/1.01  --inst_eq_res_simp                      false
% 2.48/1.01  --inst_subs_given                       false
% 2.48/1.01  --inst_orphan_elimination               true
% 2.48/1.01  --inst_learning_loop_flag               true
% 2.48/1.01  --inst_learning_start                   3000
% 2.48/1.01  --inst_learning_factor                  2
% 2.48/1.01  --inst_start_prop_sim_after_learn       3
% 2.48/1.01  --inst_sel_renew                        solver
% 2.48/1.01  --inst_lit_activity_flag                true
% 2.48/1.01  --inst_restr_to_given                   false
% 2.48/1.01  --inst_activity_threshold               500
% 2.48/1.01  --inst_out_proof                        true
% 2.48/1.01  
% 2.48/1.01  ------ Resolution Options
% 2.48/1.01  
% 2.48/1.01  --resolution_flag                       true
% 2.48/1.01  --res_lit_sel                           adaptive
% 2.48/1.01  --res_lit_sel_side                      none
% 2.48/1.01  --res_ordering                          kbo
% 2.48/1.01  --res_to_prop_solver                    active
% 2.48/1.01  --res_prop_simpl_new                    false
% 2.48/1.01  --res_prop_simpl_given                  true
% 2.48/1.01  --res_passive_queue_type                priority_queues
% 2.48/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.01  --res_passive_queues_freq               [15;5]
% 2.48/1.01  --res_forward_subs                      full
% 2.48/1.01  --res_backward_subs                     full
% 2.48/1.01  --res_forward_subs_resolution           true
% 2.48/1.01  --res_backward_subs_resolution          true
% 2.48/1.01  --res_orphan_elimination                true
% 2.48/1.01  --res_time_limit                        2.
% 2.48/1.01  --res_out_proof                         true
% 2.48/1.01  
% 2.48/1.01  ------ Superposition Options
% 2.48/1.01  
% 2.48/1.01  --superposition_flag                    true
% 2.48/1.01  --sup_passive_queue_type                priority_queues
% 2.48/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.01  --demod_completeness_check              fast
% 2.48/1.01  --demod_use_ground                      true
% 2.48/1.01  --sup_to_prop_solver                    passive
% 2.48/1.01  --sup_prop_simpl_new                    true
% 2.48/1.01  --sup_prop_simpl_given                  true
% 2.48/1.01  --sup_fun_splitting                     false
% 2.48/1.01  --sup_smt_interval                      50000
% 2.48/1.01  
% 2.48/1.01  ------ Superposition Simplification Setup
% 2.48/1.01  
% 2.48/1.01  --sup_indices_passive                   []
% 2.48/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.01  --sup_full_bw                           [BwDemod]
% 2.48/1.01  --sup_immed_triv                        [TrivRules]
% 2.48/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.01  --sup_immed_bw_main                     []
% 2.48/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.01  
% 2.48/1.01  ------ Combination Options
% 2.48/1.01  
% 2.48/1.01  --comb_res_mult                         3
% 2.48/1.01  --comb_sup_mult                         2
% 2.48/1.01  --comb_inst_mult                        10
% 2.48/1.01  
% 2.48/1.01  ------ Debug Options
% 2.48/1.01  
% 2.48/1.01  --dbg_backtrace                         false
% 2.48/1.01  --dbg_dump_prop_clauses                 false
% 2.48/1.01  --dbg_dump_prop_clauses_file            -
% 2.48/1.01  --dbg_out_stat                          false
% 2.48/1.01  ------ Parsing...
% 2.48/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.01  
% 2.48/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.48/1.01  
% 2.48/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.01  
% 2.48/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.48/1.01  ------ Proving...
% 2.48/1.01  ------ Problem Properties 
% 2.48/1.01  
% 2.48/1.01  
% 2.48/1.01  clauses                                 9
% 2.48/1.01  conjectures                             1
% 2.48/1.01  EPR                                     0
% 2.48/1.01  Horn                                    9
% 2.48/1.01  unary                                   9
% 2.48/1.01  binary                                  0
% 2.48/1.01  lits                                    9
% 2.48/1.01  lits eq                                 9
% 2.48/1.01  fd_pure                                 0
% 2.48/1.01  fd_pseudo                               0
% 2.48/1.01  fd_cond                                 0
% 2.48/1.01  fd_pseudo_cond                          0
% 2.48/1.01  AC symbols                              0
% 2.48/1.01  
% 2.48/1.01  ------ Schedule UEQ
% 2.48/1.01  
% 2.48/1.01  ------ pure equality problem: resolution off 
% 2.48/1.01  
% 2.48/1.01  ------ Option_UEQ Time Limit: Unbounded
% 2.48/1.01  
% 2.48/1.01  
% 2.48/1.01  ------ 
% 2.48/1.01  Current options:
% 2.48/1.01  ------ 
% 2.48/1.01  
% 2.48/1.01  ------ Input Options
% 2.48/1.01  
% 2.48/1.01  --out_options                           all
% 2.48/1.01  --tptp_safe_out                         true
% 2.48/1.01  --problem_path                          ""
% 2.48/1.01  --include_path                          ""
% 2.48/1.01  --clausifier                            res/vclausify_rel
% 2.48/1.01  --clausifier_options                    --mode clausify
% 2.48/1.01  --stdin                                 false
% 2.48/1.01  --stats_out                             all
% 2.48/1.01  
% 2.48/1.01  ------ General Options
% 2.48/1.01  
% 2.48/1.01  --fof                                   false
% 2.48/1.01  --time_out_real                         305.
% 2.48/1.02  --time_out_virtual                      -1.
% 2.48/1.02  --symbol_type_check                     false
% 2.48/1.02  --clausify_out                          false
% 2.48/1.02  --sig_cnt_out                           false
% 2.48/1.02  --trig_cnt_out                          false
% 2.48/1.02  --trig_cnt_out_tolerance                1.
% 2.48/1.02  --trig_cnt_out_sk_spl                   false
% 2.48/1.02  --abstr_cl_out                          false
% 2.48/1.02  
% 2.48/1.02  ------ Global Options
% 2.48/1.02  
% 2.48/1.02  --schedule                              default
% 2.48/1.02  --add_important_lit                     false
% 2.48/1.02  --prop_solver_per_cl                    1000
% 2.48/1.02  --min_unsat_core                        false
% 2.48/1.02  --soft_assumptions                      false
% 2.48/1.02  --soft_lemma_size                       3
% 2.48/1.02  --prop_impl_unit_size                   0
% 2.48/1.02  --prop_impl_unit                        []
% 2.48/1.02  --share_sel_clauses                     true
% 2.48/1.02  --reset_solvers                         false
% 2.48/1.02  --bc_imp_inh                            [conj_cone]
% 2.48/1.02  --conj_cone_tolerance                   3.
% 2.48/1.02  --extra_neg_conj                        none
% 2.48/1.02  --large_theory_mode                     true
% 2.48/1.02  --prolific_symb_bound                   200
% 2.48/1.02  --lt_threshold                          2000
% 2.48/1.02  --clause_weak_htbl                      true
% 2.48/1.02  --gc_record_bc_elim                     false
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing Options
% 2.48/1.02  
% 2.48/1.02  --preprocessing_flag                    true
% 2.48/1.02  --time_out_prep_mult                    0.1
% 2.48/1.02  --splitting_mode                        input
% 2.48/1.02  --splitting_grd                         true
% 2.48/1.02  --splitting_cvd                         false
% 2.48/1.02  --splitting_cvd_svl                     false
% 2.48/1.02  --splitting_nvd                         32
% 2.48/1.02  --sub_typing                            true
% 2.48/1.02  --prep_gs_sim                           true
% 2.48/1.02  --prep_unflatten                        true
% 2.48/1.02  --prep_res_sim                          true
% 2.48/1.02  --prep_upred                            true
% 2.48/1.02  --prep_sem_filter                       exhaustive
% 2.48/1.02  --prep_sem_filter_out                   false
% 2.48/1.02  --pred_elim                             true
% 2.48/1.02  --res_sim_input                         true
% 2.48/1.02  --eq_ax_congr_red                       true
% 2.48/1.02  --pure_diseq_elim                       true
% 2.48/1.02  --brand_transform                       false
% 2.48/1.02  --non_eq_to_eq                          false
% 2.48/1.02  --prep_def_merge                        true
% 2.48/1.02  --prep_def_merge_prop_impl              false
% 2.48/1.02  --prep_def_merge_mbd                    true
% 2.48/1.02  --prep_def_merge_tr_red                 false
% 2.48/1.02  --prep_def_merge_tr_cl                  false
% 2.48/1.02  --smt_preprocessing                     true
% 2.48/1.02  --smt_ac_axioms                         fast
% 2.48/1.02  --preprocessed_out                      false
% 2.48/1.02  --preprocessed_stats                    false
% 2.48/1.02  
% 2.48/1.02  ------ Abstraction refinement Options
% 2.48/1.02  
% 2.48/1.02  --abstr_ref                             []
% 2.48/1.02  --abstr_ref_prep                        false
% 2.48/1.02  --abstr_ref_until_sat                   false
% 2.48/1.02  --abstr_ref_sig_restrict                funpre
% 2.48/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.02  --abstr_ref_under                       []
% 2.48/1.02  
% 2.48/1.02  ------ SAT Options
% 2.48/1.02  
% 2.48/1.02  --sat_mode                              false
% 2.48/1.02  --sat_fm_restart_options                ""
% 2.48/1.02  --sat_gr_def                            false
% 2.48/1.02  --sat_epr_types                         true
% 2.48/1.02  --sat_non_cyclic_types                  false
% 2.48/1.02  --sat_finite_models                     false
% 2.48/1.02  --sat_fm_lemmas                         false
% 2.48/1.02  --sat_fm_prep                           false
% 2.48/1.02  --sat_fm_uc_incr                        true
% 2.48/1.02  --sat_out_model                         small
% 2.48/1.02  --sat_out_clauses                       false
% 2.48/1.02  
% 2.48/1.02  ------ QBF Options
% 2.48/1.02  
% 2.48/1.02  --qbf_mode                              false
% 2.48/1.02  --qbf_elim_univ                         false
% 2.48/1.02  --qbf_dom_inst                          none
% 2.48/1.02  --qbf_dom_pre_inst                      false
% 2.48/1.02  --qbf_sk_in                             false
% 2.48/1.02  --qbf_pred_elim                         true
% 2.48/1.02  --qbf_split                             512
% 2.48/1.02  
% 2.48/1.02  ------ BMC1 Options
% 2.48/1.02  
% 2.48/1.02  --bmc1_incremental                      false
% 2.48/1.02  --bmc1_axioms                           reachable_all
% 2.48/1.02  --bmc1_min_bound                        0
% 2.48/1.02  --bmc1_max_bound                        -1
% 2.48/1.02  --bmc1_max_bound_default                -1
% 2.48/1.02  --bmc1_symbol_reachability              true
% 2.48/1.02  --bmc1_property_lemmas                  false
% 2.48/1.02  --bmc1_k_induction                      false
% 2.48/1.02  --bmc1_non_equiv_states                 false
% 2.48/1.02  --bmc1_deadlock                         false
% 2.48/1.02  --bmc1_ucm                              false
% 2.48/1.02  --bmc1_add_unsat_core                   none
% 2.48/1.02  --bmc1_unsat_core_children              false
% 2.48/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.02  --bmc1_out_stat                         full
% 2.48/1.02  --bmc1_ground_init                      false
% 2.48/1.02  --bmc1_pre_inst_next_state              false
% 2.48/1.02  --bmc1_pre_inst_state                   false
% 2.48/1.02  --bmc1_pre_inst_reach_state             false
% 2.48/1.02  --bmc1_out_unsat_core                   false
% 2.48/1.02  --bmc1_aig_witness_out                  false
% 2.48/1.02  --bmc1_verbose                          false
% 2.48/1.02  --bmc1_dump_clauses_tptp                false
% 2.48/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.02  --bmc1_dump_file                        -
% 2.48/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.02  --bmc1_ucm_extend_mode                  1
% 2.48/1.02  --bmc1_ucm_init_mode                    2
% 2.48/1.02  --bmc1_ucm_cone_mode                    none
% 2.48/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.02  --bmc1_ucm_relax_model                  4
% 2.48/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.02  --bmc1_ucm_layered_model                none
% 2.48/1.02  --bmc1_ucm_max_lemma_size               10
% 2.48/1.02  
% 2.48/1.02  ------ AIG Options
% 2.48/1.02  
% 2.48/1.02  --aig_mode                              false
% 2.48/1.02  
% 2.48/1.02  ------ Instantiation Options
% 2.48/1.02  
% 2.48/1.02  --instantiation_flag                    false
% 2.48/1.02  --inst_sos_flag                         false
% 2.48/1.02  --inst_sos_phase                        true
% 2.48/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel_side                     num_symb
% 2.48/1.02  --inst_solver_per_active                1400
% 2.48/1.02  --inst_solver_calls_frac                1.
% 2.48/1.02  --inst_passive_queue_type               priority_queues
% 2.48/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.02  --inst_passive_queues_freq              [25;2]
% 2.48/1.02  --inst_dismatching                      true
% 2.48/1.02  --inst_eager_unprocessed_to_passive     true
% 2.48/1.02  --inst_prop_sim_given                   true
% 2.48/1.02  --inst_prop_sim_new                     false
% 2.48/1.02  --inst_subs_new                         false
% 2.48/1.02  --inst_eq_res_simp                      false
% 2.48/1.02  --inst_subs_given                       false
% 2.48/1.02  --inst_orphan_elimination               true
% 2.48/1.02  --inst_learning_loop_flag               true
% 2.48/1.02  --inst_learning_start                   3000
% 2.48/1.02  --inst_learning_factor                  2
% 2.48/1.02  --inst_start_prop_sim_after_learn       3
% 2.48/1.02  --inst_sel_renew                        solver
% 2.48/1.02  --inst_lit_activity_flag                true
% 2.48/1.02  --inst_restr_to_given                   false
% 2.48/1.02  --inst_activity_threshold               500
% 2.48/1.02  --inst_out_proof                        true
% 2.48/1.02  
% 2.48/1.02  ------ Resolution Options
% 2.48/1.02  
% 2.48/1.02  --resolution_flag                       false
% 2.48/1.02  --res_lit_sel                           adaptive
% 2.48/1.02  --res_lit_sel_side                      none
% 2.48/1.02  --res_ordering                          kbo
% 2.48/1.02  --res_to_prop_solver                    active
% 2.48/1.02  --res_prop_simpl_new                    false
% 2.48/1.02  --res_prop_simpl_given                  true
% 2.48/1.02  --res_passive_queue_type                priority_queues
% 2.48/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.02  --res_passive_queues_freq               [15;5]
% 2.48/1.02  --res_forward_subs                      full
% 2.48/1.02  --res_backward_subs                     full
% 2.48/1.02  --res_forward_subs_resolution           true
% 2.48/1.02  --res_backward_subs_resolution          true
% 2.48/1.02  --res_orphan_elimination                true
% 2.48/1.02  --res_time_limit                        2.
% 2.48/1.02  --res_out_proof                         true
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Options
% 2.48/1.02  
% 2.48/1.02  --superposition_flag                    true
% 2.48/1.02  --sup_passive_queue_type                priority_queues
% 2.48/1.02  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.02  --demod_completeness_check              fast
% 2.48/1.02  --demod_use_ground                      true
% 2.48/1.02  --sup_to_prop_solver                    active
% 2.48/1.02  --sup_prop_simpl_new                    false
% 2.48/1.02  --sup_prop_simpl_given                  false
% 2.48/1.02  --sup_fun_splitting                     true
% 2.48/1.02  --sup_smt_interval                      10000
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Simplification Setup
% 2.48/1.02  
% 2.48/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.48/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_full_triv                         [TrivRules]
% 2.48/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.48/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.48/1.02  --sup_immed_triv                        [TrivRules]
% 2.48/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_bw_main                     []
% 2.48/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.48/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.48/1.02  
% 2.48/1.02  ------ Combination Options
% 2.48/1.02  
% 2.48/1.02  --comb_res_mult                         1
% 2.48/1.02  --comb_sup_mult                         1
% 2.48/1.02  --comb_inst_mult                        1000000
% 2.48/1.02  
% 2.48/1.02  ------ Debug Options
% 2.48/1.02  
% 2.48/1.02  --dbg_backtrace                         false
% 2.48/1.02  --dbg_dump_prop_clauses                 false
% 2.48/1.02  --dbg_dump_prop_clauses_file            -
% 2.48/1.02  --dbg_out_stat                          false
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  ------ Proving...
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  % SZS status Theorem for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02   Resolution empty clause
% 2.48/1.02  
% 2.48/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  fof(f3,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f23,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f3])).
% 2.48/1.02  
% 2.48/1.02  fof(f12,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f32,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f12])).
% 2.48/1.02  
% 2.48/1.02  fof(f43,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f23,f32,f32])).
% 2.48/1.02  
% 2.48/1.02  fof(f4,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f24,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f4])).
% 2.48/1.02  
% 2.48/1.02  fof(f44,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f24,f32,f32])).
% 2.48/1.02  
% 2.48/1.02  fof(f6,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f26,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f6])).
% 2.48/1.02  
% 2.48/1.02  fof(f10,axiom,(
% 2.48/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f30,plain,(
% 2.48/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f10])).
% 2.48/1.02  
% 2.48/1.02  fof(f39,plain,(
% 2.48/1.02    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f30,f37])).
% 2.48/1.02  
% 2.48/1.02  fof(f2,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f22,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f2])).
% 2.48/1.02  
% 2.48/1.02  fof(f1,axiom,(
% 2.48/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f21,plain,(
% 2.48/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.48/1.02    inference(cnf_transformation,[],[f1])).
% 2.48/1.02  
% 2.48/1.02  fof(f11,axiom,(
% 2.48/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f31,plain,(
% 2.48/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f11])).
% 2.48/1.02  
% 2.48/1.02  fof(f37,plain,(
% 2.48/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f31,f32])).
% 2.48/1.02  
% 2.48/1.02  fof(f38,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f22,f21,f32,f37])).
% 2.48/1.02  
% 2.48/1.02  fof(f46,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k2_enumset1(X0,X1,X2,X3)))) )),
% 2.48/1.02    inference(definition_unfolding,[],[f26,f21,f39,f38])).
% 2.48/1.02  
% 2.48/1.02  fof(f13,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f33,plain,(
% 2.48/1.02    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f13])).
% 2.48/1.02  
% 2.48/1.02  fof(f42,plain,(
% 2.48/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f33,f38])).
% 2.48/1.02  
% 2.48/1.02  fof(f15,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f35,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f15])).
% 2.48/1.02  
% 2.48/1.02  fof(f49,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f35,f32,f32])).
% 2.48/1.02  
% 2.48/1.02  fof(f5,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f25,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f5])).
% 2.48/1.02  
% 2.48/1.02  fof(f45,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2)))) )),
% 2.48/1.02    inference(definition_unfolding,[],[f25,f21,f37,f32,f38])).
% 2.48/1.02  
% 2.48/1.02  fof(f16,conjecture,(
% 2.48/1.02    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f17,negated_conjecture,(
% 2.48/1.02    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.48/1.02    inference(negated_conjecture,[],[f16])).
% 2.48/1.02  
% 2.48/1.02  fof(f18,plain,(
% 2.48/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.48/1.02    inference(ennf_transformation,[],[f17])).
% 2.48/1.02  
% 2.48/1.02  fof(f19,plain,(
% 2.48/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.48/1.02    introduced(choice_axiom,[])).
% 2.48/1.02  
% 2.48/1.02  fof(f20,plain,(
% 2.48/1.02    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.48/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 2.48/1.02  
% 2.48/1.02  fof(f36,plain,(
% 2.48/1.02    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.48/1.02    inference(cnf_transformation,[],[f20])).
% 2.48/1.02  
% 2.48/1.02  fof(f50,plain,(
% 2.48/1.02    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 2.48/1.02    inference(definition_unfolding,[],[f36,f21,f37,f37,f32])).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1,plain,
% 2.48/1.02      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X0,X1) ),
% 2.48/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_25,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X2_36,X2_36,X0_36,X1_36) ),
% 2.48/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2,plain,
% 2.48/1.02      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
% 2.48/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_24,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X2_36,X2_36,X1_36,X0_36) ),
% 2.48/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_69,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X1_36,X1_36,X0_36,X2_36) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_25,c_24]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) ),
% 2.48/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_22,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X1_36,X2_36,X3_36),k4_xboole_0(k2_enumset1(X4_36,X4_36,X4_36,X4_36),k2_enumset1(X0_36,X1_36,X2_36,X3_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X4_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) ),
% 2.48/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_269,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X1_36,X1_36,X0_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X1_36,X1_36,X0_36,X2_36))) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_69,c_22]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_0,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
% 2.48/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_26,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
% 2.48/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_312,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_22,c_26]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_7,plain,
% 2.48/1.02      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
% 2.48/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_19,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X0_36,X0_36,X2_36,X1_36) ),
% 2.48/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_45,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X0_36,X1_36,X2_36) = k2_enumset1(X1_36,X1_36,X2_36,X0_36) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_24,c_19]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_270,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X2_36,X2_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X2_36,X2_36,X0_36,X1_36))) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_45,c_22]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_318,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X2_36,X0_36,X1_36,X3_36) ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_270,c_312]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_319,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X2_36,X1_36,X0_36,X3_36) ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_269,c_312,c_318]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_511,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X1_36,X1_36,X2_36) = k2_enumset1(X0_36,X0_36,X2_36,X1_36) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_319,c_25]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_265,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X2_36,X1_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X2_36,X1_36))) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_19,c_22]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_322,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X1_36,X0_36,X2_36,X3_36) ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_265,c_312,c_318]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))) ),
% 2.48/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_23,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X4_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X4_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) ),
% 2.48/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_393,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_23,c_22]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_141,plain,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X3_36,X2_36) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_45,c_26]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_409,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X1_36,X2_36,X3_36,X0_36) ),
% 2.48/1.02      inference(light_normalisation,[status(thm)],[c_393,c_141,c_318]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_723,plain,
% 2.48/1.02      ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X0_36,X3_36,X1_36,X2_36) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_322,c_409]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_8,negated_conjecture,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 2.48/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_18,negated_conjecture,
% 2.48/1.02      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 2.48/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_40,plain,
% 2.48/1.02      ( k2_enumset1(sK1,sK0,sK2,sK0) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_18,c_26]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_49,plain,
% 2.48/1.02      ( k2_enumset1(sK1,sK1,sK2,sK0) != k2_enumset1(sK1,sK0,sK2,sK0) ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_25,c_40]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2467,plain,
% 2.48/1.02      ( k2_enumset1(sK1,sK0,sK0,sK2) != k2_enumset1(sK1,sK1,sK2,sK0) ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_723,c_49]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2695,plain,
% 2.48/1.02      ( $false ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_511,c_2467]) ).
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  ------                               Statistics
% 2.48/1.02  
% 2.48/1.02  ------ General
% 2.48/1.02  
% 2.48/1.02  abstr_ref_over_cycles:                  0
% 2.48/1.02  abstr_ref_under_cycles:                 0
% 2.48/1.02  gc_basic_clause_elim:                   0
% 2.48/1.02  forced_gc_time:                         0
% 2.48/1.02  parsing_time:                           0.017
% 2.48/1.02  unif_index_cands_time:                  0.
% 2.48/1.02  unif_index_add_time:                    0.
% 2.48/1.02  orderings_time:                         0.
% 2.48/1.02  out_proof_time:                         0.016
% 2.48/1.02  total_time:                             0.201
% 2.48/1.02  num_of_symbols:                         37
% 2.48/1.02  num_of_terms:                           2542
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing
% 2.48/1.02  
% 2.48/1.02  num_of_splits:                          0
% 2.48/1.02  num_of_split_atoms:                     0
% 2.48/1.02  num_of_reused_defs:                     0
% 2.48/1.02  num_eq_ax_congr_red:                    4
% 2.48/1.02  num_of_sem_filtered_clauses:            0
% 2.48/1.02  num_of_subtypes:                        3
% 2.48/1.02  monotx_restored_types:                  0
% 2.48/1.02  sat_num_of_epr_types:                   0
% 2.48/1.02  sat_num_of_non_cyclic_types:            0
% 2.48/1.02  sat_guarded_non_collapsed_types:        0
% 2.48/1.02  num_pure_diseq_elim:                    0
% 2.48/1.02  simp_replaced_by:                       0
% 2.48/1.02  res_preprocessed:                       23
% 2.48/1.02  prep_upred:                             0
% 2.48/1.02  prep_unflattend:                        0
% 2.48/1.02  smt_new_axioms:                         0
% 2.48/1.02  pred_elim_cands:                        0
% 2.48/1.02  pred_elim:                              0
% 2.48/1.02  pred_elim_cl:                           0
% 2.48/1.02  pred_elim_cycles:                       0
% 2.48/1.02  merged_defs:                            0
% 2.48/1.02  merged_defs_ncl:                        0
% 2.48/1.02  bin_hyper_res:                          0
% 2.48/1.02  prep_cycles:                            2
% 2.48/1.02  pred_elim_time:                         0.
% 2.48/1.02  splitting_time:                         0.
% 2.48/1.02  sem_filter_time:                        0.
% 2.48/1.02  monotx_time:                            0.
% 2.48/1.02  subtype_inf_time:                       0.001
% 2.48/1.02  
% 2.48/1.02  ------ Problem properties
% 2.48/1.02  
% 2.48/1.02  clauses:                                9
% 2.48/1.02  conjectures:                            1
% 2.48/1.02  epr:                                    0
% 2.48/1.02  horn:                                   9
% 2.48/1.02  ground:                                 1
% 2.48/1.02  unary:                                  9
% 2.48/1.02  binary:                                 0
% 2.48/1.02  lits:                                   9
% 2.48/1.02  lits_eq:                                9
% 2.48/1.02  fd_pure:                                0
% 2.48/1.02  fd_pseudo:                              0
% 2.48/1.02  fd_cond:                                0
% 2.48/1.02  fd_pseudo_cond:                         0
% 2.48/1.02  ac_symbols:                             0
% 2.48/1.02  
% 2.48/1.02  ------ Propositional Solver
% 2.48/1.02  
% 2.48/1.02  prop_solver_calls:                      13
% 2.48/1.02  prop_fast_solver_calls:                 58
% 2.48/1.02  smt_solver_calls:                       0
% 2.48/1.02  smt_fast_solver_calls:                  0
% 2.48/1.02  prop_num_of_clauses:                    59
% 2.48/1.02  prop_preprocess_simplified:             327
% 2.48/1.02  prop_fo_subsumed:                       0
% 2.48/1.02  prop_solver_time:                       0.
% 2.48/1.02  smt_solver_time:                        0.
% 2.48/1.02  smt_fast_solver_time:                   0.
% 2.48/1.02  prop_fast_solver_time:                  0.
% 2.48/1.02  prop_unsat_core_time:                   0.
% 2.48/1.02  
% 2.48/1.02  ------ QBF
% 2.48/1.02  
% 2.48/1.02  qbf_q_res:                              0
% 2.48/1.02  qbf_num_tautologies:                    0
% 2.48/1.02  qbf_prep_cycles:                        0
% 2.48/1.02  
% 2.48/1.02  ------ BMC1
% 2.48/1.02  
% 2.48/1.02  bmc1_current_bound:                     -1
% 2.48/1.02  bmc1_last_solved_bound:                 -1
% 2.48/1.02  bmc1_unsat_core_size:                   -1
% 2.48/1.02  bmc1_unsat_core_parents_size:           -1
% 2.48/1.02  bmc1_merge_next_fun:                    0
% 2.48/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.02  
% 2.48/1.02  ------ Instantiation
% 2.48/1.02  
% 2.48/1.02  inst_num_of_clauses:                    0
% 2.48/1.02  inst_num_in_passive:                    0
% 2.48/1.02  inst_num_in_active:                     0
% 2.48/1.02  inst_num_in_unprocessed:                0
% 2.48/1.02  inst_num_of_loops:                      0
% 2.48/1.02  inst_num_of_learning_restarts:          0
% 2.48/1.02  inst_num_moves_active_passive:          0
% 2.48/1.02  inst_lit_activity:                      0
% 2.48/1.02  inst_lit_activity_moves:                0
% 2.48/1.02  inst_num_tautologies:                   0
% 2.48/1.02  inst_num_prop_implied:                  0
% 2.48/1.02  inst_num_existing_simplified:           0
% 2.48/1.02  inst_num_eq_res_simplified:             0
% 2.48/1.02  inst_num_child_elim:                    0
% 2.48/1.02  inst_num_of_dismatching_blockings:      0
% 2.48/1.02  inst_num_of_non_proper_insts:           0
% 2.48/1.02  inst_num_of_duplicates:                 0
% 2.48/1.02  inst_inst_num_from_inst_to_res:         0
% 2.48/1.02  inst_dismatching_checking_time:         0.
% 2.48/1.02  
% 2.48/1.02  ------ Resolution
% 2.48/1.02  
% 2.48/1.02  res_num_of_clauses:                     0
% 2.48/1.02  res_num_in_passive:                     0
% 2.48/1.02  res_num_in_active:                      0
% 2.48/1.02  res_num_of_loops:                       25
% 2.48/1.02  res_forward_subset_subsumed:            0
% 2.48/1.02  res_backward_subset_subsumed:           0
% 2.48/1.02  res_forward_subsumed:                   0
% 2.48/1.02  res_backward_subsumed:                  0
% 2.48/1.02  res_forward_subsumption_resolution:     0
% 2.48/1.02  res_backward_subsumption_resolution:    0
% 2.48/1.02  res_clause_to_clause_subsumption:       5897
% 2.48/1.02  res_orphan_elimination:                 0
% 2.48/1.02  res_tautology_del:                      0
% 2.48/1.02  res_num_eq_res_simplified:              0
% 2.48/1.02  res_num_sel_changes:                    0
% 2.48/1.02  res_moves_from_active_to_pass:          0
% 2.48/1.02  
% 2.48/1.02  ------ Superposition
% 2.48/1.02  
% 2.48/1.02  sup_time_total:                         0.
% 2.48/1.02  sup_time_generating:                    0.
% 2.48/1.02  sup_time_sim_full:                      0.
% 2.48/1.02  sup_time_sim_immed:                     0.
% 2.48/1.02  
% 2.48/1.02  sup_num_of_clauses:                     360
% 2.48/1.02  sup_num_in_active:                      30
% 2.48/1.02  sup_num_in_passive:                     330
% 2.48/1.02  sup_num_of_loops:                       31
% 2.48/1.02  sup_fw_superposition:                   1089
% 2.48/1.02  sup_bw_superposition:                   1505
% 2.48/1.02  sup_immediate_simplified:               74
% 2.48/1.02  sup_given_eliminated:                   0
% 2.48/1.02  comparisons_done:                       0
% 2.48/1.02  comparisons_avoided:                    0
% 2.48/1.02  
% 2.48/1.02  ------ Simplifications
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  sim_fw_subset_subsumed:                 0
% 2.48/1.02  sim_bw_subset_subsumed:                 0
% 2.48/1.02  sim_fw_subsumed:                        16
% 2.48/1.02  sim_bw_subsumed:                        3
% 2.48/1.02  sim_fw_subsumption_res:                 0
% 2.48/1.02  sim_bw_subsumption_res:                 0
% 2.48/1.02  sim_tautology_del:                      0
% 2.48/1.02  sim_eq_tautology_del:                   5
% 2.48/1.02  sim_eq_res_simp:                        0
% 2.48/1.02  sim_fw_demodulated:                     30
% 2.48/1.02  sim_bw_demodulated:                     2
% 2.48/1.02  sim_light_normalised:                   29
% 2.48/1.02  sim_joinable_taut:                      0
% 2.48/1.02  sim_joinable_simp:                      0
% 2.48/1.02  sim_ac_normalised:                      0
% 2.48/1.02  sim_smt_subsumption:                    0
% 2.48/1.02  
%------------------------------------------------------------------------------
