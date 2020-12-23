%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:24 EST 2020

% Result     : Theorem 22.63s
% Output     : CNFRefutation 22.63s
% Verified   : 
% Statistics : Number of formulae       :  107 (1866 expanded)
%              Number of clauses        :   63 ( 383 expanded)
%              Number of leaves         :   15 ( 565 expanded)
%              Depth                    :   20
%              Number of atoms          :  108 (1867 expanded)
%              Number of equality atoms :  107 (1866 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f37,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f21,f19,f28])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f24,f19,f34])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f30,f35,f36])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f23,f19,f35])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f34,f34])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f32,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f32,f19,f34,f34,f33])).

cnf(c_0,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_26,plain,
    ( k3_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38) = k1_tarski(X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_25,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_197,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k1_tarski(X1_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X1_38,X1_38,X1_38) ),
    inference(superposition,[status(thm)],[c_26,c_25])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k3_enumset1(X4_38,X4_38,X4_38,X4_38,X5_38),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X5_38),k1_tarski(X0_38))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_313,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k5_xboole_0(k1_tarski(X4_38),k4_xboole_0(k1_tarski(X4_38),k1_tarski(X4_38))),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) ),
    inference(superposition,[status(thm)],[c_197,c_21])).

cnf(c_3,plain,
    ( k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k1_tarski(X5_38),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X5_38),k1_tarski(X0_38))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_186,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k1_tarski(X0_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38) ),
    inference(superposition,[status(thm)],[c_26,c_22])).

cnf(c_188,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k1_tarski(X0_38),k1_tarski(X0_38))) = k1_tarski(X0_38) ),
    inference(light_normalisation,[status(thm)],[c_186,c_26])).

cnf(c_332,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) ),
    inference(demodulation,[status(thm)],[c_313,c_23,c_188])).

cnf(c_333,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
    inference(light_normalisation,[status(thm)],[c_332,c_22])).

cnf(c_769,plain,
    ( k3_enumset1(X0_38,X1_38,X2_38,X3_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
    inference(superposition,[status(thm)],[c_333,c_22])).

cnf(c_847,plain,
    ( k3_enumset1(X0_38,X1_38,X2_38,X2_38,X2_38) = k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38) ),
    inference(superposition,[status(thm)],[c_769,c_769])).

cnf(c_2,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_24,plain,
    ( k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38) = k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_838,plain,
    ( k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38) = k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38) ),
    inference(superposition,[status(thm)],[c_769,c_24])).

cnf(c_770,plain,
    ( k3_enumset1(X0_38,X1_38,X2_38,X3_38,X3_38) = k3_enumset1(X0_38,X1_38,X1_38,X2_38,X3_38) ),
    inference(superposition,[status(thm)],[c_333,c_25])).

cnf(c_1394,plain,
    ( k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38) = k3_enumset1(X1_38,X1_38,X1_38,X0_38,X0_38) ),
    inference(superposition,[status(thm)],[c_838,c_770])).

cnf(c_6729,plain,
    ( k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38) = k3_enumset1(X1_38,X0_38,X0_38,X0_38,X0_38) ),
    inference(superposition,[status(thm)],[c_847,c_1394])).

cnf(c_53121,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38),k4_xboole_0(k1_tarski(X2_38),k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38))) = k5_xboole_0(k1_tarski(X1_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38),k1_tarski(X1_38))) ),
    inference(superposition,[status(thm)],[c_6729,c_23])).

cnf(c_312,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k1_tarski(X4_38),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) ),
    inference(superposition,[status(thm)],[c_26,c_21])).

cnf(c_335,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k1_tarski(X4_38),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
    inference(light_normalisation,[status(thm)],[c_312,c_333])).

cnf(c_53184,plain,
    ( k3_enumset1(X0_38,X1_38,X1_38,X1_38,X2_38) = k3_enumset1(X1_38,X1_38,X0_38,X0_38,X2_38) ),
    inference(demodulation,[status(thm)],[c_53121,c_25,c_335])).

cnf(c_54973,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X1_38,X2_38),k4_xboole_0(k1_tarski(X3_38),k3_enumset1(X0_38,X0_38,X1_38,X1_38,X2_38))) = k5_xboole_0(k1_tarski(X1_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X2_38,X3_38),k1_tarski(X1_38))) ),
    inference(superposition,[status(thm)],[c_53184,c_23])).

cnf(c_55320,plain,
    ( k3_enumset1(X0_38,X1_38,X1_38,X2_38,X3_38) = k3_enumset1(X1_38,X0_38,X0_38,X2_38,X3_38) ),
    inference(demodulation,[status(thm)],[c_54973,c_25,c_335])).

cnf(c_184,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38) ),
    inference(superposition,[status(thm)],[c_24,c_22])).

cnf(c_286,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38),k1_tarski(X0_38))),k4_xboole_0(k1_tarski(X2_38),k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38),k1_tarski(X0_38))))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38),k1_tarski(X0_38))) ),
    inference(superposition,[status(thm)],[c_184,c_23])).

cnf(c_298,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X0_38,X2_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38) ),
    inference(demodulation,[status(thm)],[c_286,c_22,c_23,c_25])).

cnf(c_717,plain,
    ( k3_enumset1(X0_38,X1_38,X1_38,X0_38,X2_38) = k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38) ),
    inference(superposition,[status(thm)],[c_298,c_25])).

cnf(c_224,plain,
    ( k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38) = k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38) ),
    inference(superposition,[status(thm)],[c_184,c_25])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k3_enumset1(X5_38,X5_38,X5_38,X5_38,X6_38),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38,X6_38) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_358,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38),k4_xboole_0(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X3_38),k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38))) = k6_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) ),
    inference(superposition,[status(thm)],[c_224,c_20])).

cnf(c_362,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38),k4_xboole_0(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X3_38),k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))) ),
    inference(superposition,[status(thm)],[c_224,c_21])).

cnf(c_376,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38),k4_xboole_0(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X3_38),k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38))) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
    inference(demodulation,[status(thm)],[c_362,c_20,c_22])).

cnf(c_380,plain,
    ( k6_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
    inference(light_normalisation,[status(thm)],[c_358,c_376])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_174,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_20,c_19])).

cnf(c_473,plain,
    ( k3_enumset1(sK1,sK1,sK0,sK2,sK0) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_380,c_174])).

cnf(c_725,plain,
    ( k3_enumset1(sK0,sK1,sK1,sK0,sK2) != k3_enumset1(sK1,sK1,sK0,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_717,c_473])).

cnf(c_55734,plain,
    ( k3_enumset1(sK1,sK0,sK0,sK0,sK2) != k3_enumset1(sK1,sK1,sK0,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_55320,c_725])).

cnf(c_195,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
    inference(superposition,[status(thm)],[c_24,c_25])).

cnf(c_500,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38),k1_tarski(X0_38))),k1_tarski(X0_38))) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
    inference(superposition,[status(thm)],[c_195,c_22])).

cnf(c_523,plain,
    ( k3_enumset1(X0_38,X1_38,X1_38,X1_38,X2_38) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
    inference(demodulation,[status(thm)],[c_500,c_22,c_25])).

cnf(c_964,plain,
    ( k3_enumset1(X0_38,X1_38,X1_38,X2_38,X2_38) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
    inference(superposition,[status(thm)],[c_770,c_523])).

cnf(c_942,plain,
    ( k3_enumset1(X0_38,X1_38,X1_38,X2_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
    inference(superposition,[status(thm)],[c_770,c_769])).

cnf(c_2338,plain,
    ( k3_enumset1(X0_38,X0_38,X1_38,X1_38,X2_38) = k3_enumset1(X0_38,X2_38,X2_38,X1_38,X1_38) ),
    inference(superposition,[status(thm)],[c_964,c_942])).

cnf(c_319,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X5_38),k1_tarski(X0_38))) = k6_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38) ),
    inference(superposition,[status(thm)],[c_21,c_20])).

cnf(c_22217,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X2_38,X2_38,X3_38),k1_tarski(X0_38))) = k6_enumset1(X0_38,X0_38,X0_38,X1_38,X3_38,X3_38,X2_38,X2_38) ),
    inference(superposition,[status(thm)],[c_2338,c_319])).

cnf(c_812,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X3_38) ),
    inference(superposition,[status(thm)],[c_769,c_22])).

cnf(c_253,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k5_xboole_0(k1_tarski(X5_38),k4_xboole_0(k1_tarski(X5_38),k1_tarski(X5_38))),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38,X5_38) ),
    inference(superposition,[status(thm)],[c_197,c_20])).

cnf(c_269,plain,
    ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k1_tarski(X5_38),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38,X5_38) ),
    inference(demodulation,[status(thm)],[c_253,c_188])).

cnf(c_7387,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))),k4_xboole_0(k1_tarski(X4_38),k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X3_38,X4_38,X4_38) ),
    inference(superposition,[status(thm)],[c_812,c_269])).

cnf(c_7551,plain,
    ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X3_38,X4_38,X4_38) ),
    inference(demodulation,[status(thm)],[c_7387,c_22,c_23])).

cnf(c_7552,plain,
    ( k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X3_38,X4_38,X4_38) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
    inference(light_normalisation,[status(thm)],[c_7551,c_22])).

cnf(c_22418,plain,
    ( k3_enumset1(X0_38,X1_38,X2_38,X2_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X3_38,X2_38) ),
    inference(demodulation,[status(thm)],[c_22217,c_25,c_7552])).

cnf(c_57048,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_55734,c_22418])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 22.63/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.63/3.50  
% 22.63/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 22.63/3.50  
% 22.63/3.50  ------  iProver source info
% 22.63/3.50  
% 22.63/3.50  git: date: 2020-06-30 10:37:57 +0100
% 22.63/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 22.63/3.50  git: non_committed_changes: false
% 22.63/3.50  git: last_make_outside_of_git: false
% 22.63/3.50  
% 22.63/3.50  ------ 
% 22.63/3.50  ------ Parsing...
% 22.63/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 22.63/3.50  
% 22.63/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 22.63/3.50  
% 22.63/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 22.63/3.50  
% 22.63/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 22.63/3.50  ------ Proving...
% 22.63/3.50  ------ Problem Properties 
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  clauses                                 8
% 22.63/3.50  conjectures                             1
% 22.63/3.50  EPR                                     0
% 22.63/3.50  Horn                                    8
% 22.63/3.50  unary                                   8
% 22.63/3.50  binary                                  0
% 22.63/3.50  lits                                    8
% 22.63/3.50  lits eq                                 8
% 22.63/3.50  fd_pure                                 0
% 22.63/3.50  fd_pseudo                               0
% 22.63/3.50  fd_cond                                 0
% 22.63/3.50  fd_pseudo_cond                          0
% 22.63/3.50  AC symbols                              0
% 22.63/3.50  
% 22.63/3.50  ------ Input Options Time Limit: Unbounded
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 22.63/3.50  Current options:
% 22.63/3.50  ------ 
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  ------ Proving...
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 22.63/3.50  
% 22.63/3.50  ------ Proving...
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 22.63/3.50  
% 22.63/3.50  ------ Proving...
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  % SZS status Theorem for theBenchmark.p
% 22.63/3.50  
% 22.63/3.50   Resolution empty clause
% 22.63/3.50  
% 22.63/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 22.63/3.50  
% 22.63/3.50  fof(f7,axiom,(
% 22.63/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f25,plain,(
% 22.63/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f7])).
% 22.63/3.50  
% 22.63/3.50  fof(f8,axiom,(
% 22.63/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f26,plain,(
% 22.63/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f8])).
% 22.63/3.50  
% 22.63/3.50  fof(f9,axiom,(
% 22.63/3.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f27,plain,(
% 22.63/3.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f9])).
% 22.63/3.50  
% 22.63/3.50  fof(f10,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f28,plain,(
% 22.63/3.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f10])).
% 22.63/3.50  
% 22.63/3.50  fof(f33,plain,(
% 22.63/3.50    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f27,f28])).
% 22.63/3.50  
% 22.63/3.50  fof(f34,plain,(
% 22.63/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f26,f33])).
% 22.63/3.50  
% 22.63/3.50  fof(f37,plain,(
% 22.63/3.50    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f25,f34])).
% 22.63/3.50  
% 22.63/3.50  fof(f3,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f21,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f3])).
% 22.63/3.50  
% 22.63/3.50  fof(f1,axiom,(
% 22.63/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f19,plain,(
% 22.63/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 22.63/3.50    inference(cnf_transformation,[],[f1])).
% 22.63/3.50  
% 22.63/3.50  fof(f38,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f21,f19,f28])).
% 22.63/3.50  
% 22.63/3.50  fof(f12,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f30,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f12])).
% 22.63/3.50  
% 22.63/3.50  fof(f4,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f22,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f4])).
% 22.63/3.50  
% 22.63/3.50  fof(f35,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f22,f19])).
% 22.63/3.50  
% 22.63/3.50  fof(f6,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f24,plain,(
% 22.63/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f6])).
% 22.63/3.50  
% 22.63/3.50  fof(f36,plain,(
% 22.63/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f24,f19,f34])).
% 22.63/3.50  
% 22.63/3.50  fof(f42,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))) )),
% 22.63/3.50    inference(definition_unfolding,[],[f30,f35,f36])).
% 22.63/3.50  
% 22.63/3.50  fof(f5,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f23,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f5])).
% 22.63/3.50  
% 22.63/3.50  fof(f40,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4)))) )),
% 22.63/3.50    inference(definition_unfolding,[],[f23,f19,f35])).
% 22.63/3.50  
% 22.63/3.50  fof(f11,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f29,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f11])).
% 22.63/3.50  
% 22.63/3.50  fof(f41,plain,(
% 22.63/3.50    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f29,f35])).
% 22.63/3.50  
% 22.63/3.50  fof(f2,axiom,(
% 22.63/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f20,plain,(
% 22.63/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f2])).
% 22.63/3.50  
% 22.63/3.50  fof(f39,plain,(
% 22.63/3.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f20,f34,f34])).
% 22.63/3.50  
% 22.63/3.50  fof(f13,axiom,(
% 22.63/3.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f31,plain,(
% 22.63/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 22.63/3.50    inference(cnf_transformation,[],[f13])).
% 22.63/3.50  
% 22.63/3.50  fof(f43,plain,(
% 22.63/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 22.63/3.50    inference(definition_unfolding,[],[f31,f36])).
% 22.63/3.50  
% 22.63/3.50  fof(f14,conjecture,(
% 22.63/3.50    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 22.63/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.63/3.50  
% 22.63/3.50  fof(f15,negated_conjecture,(
% 22.63/3.50    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 22.63/3.50    inference(negated_conjecture,[],[f14])).
% 22.63/3.50  
% 22.63/3.50  fof(f16,plain,(
% 22.63/3.50    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 22.63/3.50    inference(ennf_transformation,[],[f15])).
% 22.63/3.50  
% 22.63/3.50  fof(f17,plain,(
% 22.63/3.50    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 22.63/3.50    introduced(choice_axiom,[])).
% 22.63/3.50  
% 22.63/3.50  fof(f18,plain,(
% 22.63/3.50    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 22.63/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 22.63/3.50  
% 22.63/3.50  fof(f32,plain,(
% 22.63/3.50    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 22.63/3.50    inference(cnf_transformation,[],[f18])).
% 22.63/3.50  
% 22.63/3.50  fof(f44,plain,(
% 22.63/3.50    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 22.63/3.50    inference(definition_unfolding,[],[f32,f19,f34,f34,f33])).
% 22.63/3.50  
% 22.63/3.50  cnf(c_0,plain,
% 22.63/3.50      ( k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
% 22.63/3.50      inference(cnf_transformation,[],[f37]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_26,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38) = k1_tarski(X0_38) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_0]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_1,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 22.63/3.50      inference(cnf_transformation,[],[f38]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_25,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_1]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_197,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k1_tarski(X1_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X1_38,X1_38,X1_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_26,c_25]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_5,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ),
% 22.63/3.50      inference(cnf_transformation,[],[f42]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_21,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k3_enumset1(X4_38,X4_38,X4_38,X4_38,X5_38),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X5_38),k1_tarski(X0_38))) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_5]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_313,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k5_xboole_0(k1_tarski(X4_38),k4_xboole_0(k1_tarski(X4_38),k1_tarski(X4_38))),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_197,c_21]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_3,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ),
% 22.63/3.50      inference(cnf_transformation,[],[f40]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_23,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k1_tarski(X5_38),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X5_38),k1_tarski(X0_38))) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_3]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_4,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 22.63/3.50      inference(cnf_transformation,[],[f41]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_22,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_4]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_186,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k1_tarski(X0_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_26,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_188,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k1_tarski(X0_38),k1_tarski(X0_38))) = k1_tarski(X0_38) ),
% 22.63/3.50      inference(light_normalisation,[status(thm)],[c_186,c_26]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_332,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_313,c_23,c_188]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_333,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
% 22.63/3.50      inference(light_normalisation,[status(thm)],[c_332,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_769,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X2_38,X3_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_333,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_847,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X2_38,X2_38,X2_38) = k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_769,c_769]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_2,plain,
% 22.63/3.50      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 22.63/3.50      inference(cnf_transformation,[],[f39]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_24,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38) = k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_2]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_838,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38) = k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_769,c_24]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_770,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X2_38,X3_38,X3_38) = k3_enumset1(X0_38,X1_38,X1_38,X2_38,X3_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_333,c_25]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_1394,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38) = k3_enumset1(X1_38,X1_38,X1_38,X0_38,X0_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_838,c_770]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_6729,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38) = k3_enumset1(X1_38,X0_38,X0_38,X0_38,X0_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_847,c_1394]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_53121,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38),k4_xboole_0(k1_tarski(X2_38),k3_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38))) = k5_xboole_0(k1_tarski(X1_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38),k1_tarski(X1_38))) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_6729,c_23]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_312,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k1_tarski(X4_38),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X4_38),k1_tarski(X0_38))) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_26,c_21]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_335,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k4_xboole_0(k1_tarski(X4_38),k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
% 22.63/3.50      inference(light_normalisation,[status(thm)],[c_312,c_333]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_53184,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X1_38,X1_38,X2_38) = k3_enumset1(X1_38,X1_38,X0_38,X0_38,X2_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_53121,c_25,c_335]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_54973,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X1_38,X2_38),k4_xboole_0(k1_tarski(X3_38),k3_enumset1(X0_38,X0_38,X1_38,X1_38,X2_38))) = k5_xboole_0(k1_tarski(X1_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X2_38,X3_38),k1_tarski(X1_38))) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_53184,c_23]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_55320,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X1_38,X2_38,X3_38) = k3_enumset1(X1_38,X0_38,X0_38,X2_38,X3_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_54973,c_25,c_335]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_184,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_24,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_286,plain,
% 22.63/3.50      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38),k1_tarski(X0_38))),k4_xboole_0(k1_tarski(X2_38),k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X0_38),k1_tarski(X0_38))))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38),k1_tarski(X0_38))) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_184,c_23]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_298,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X0_38,X2_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_286,c_22,c_23,c_25]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_717,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X1_38,X0_38,X2_38) = k3_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_298,c_25]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_224,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38) = k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_184,c_25]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_6,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
% 22.63/3.50      inference(cnf_transformation,[],[f43]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_20,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k3_enumset1(X5_38,X5_38,X5_38,X5_38,X6_38),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38,X6_38) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_6]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_358,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38),k4_xboole_0(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X3_38),k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38))) = k6_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_224,c_20]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_362,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38),k4_xboole_0(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X3_38),k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38))) = k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_224,c_21]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_376,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38),k4_xboole_0(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X3_38),k3_enumset1(X0_38,X1_38,X1_38,X1_38,X0_38))) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_362,c_20,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_380,plain,
% 22.63/3.50      ( k6_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
% 22.63/3.50      inference(light_normalisation,[status(thm)],[c_358,c_376]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_7,negated_conjecture,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 22.63/3.50      inference(cnf_transformation,[],[f44]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_19,negated_conjecture,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 22.63/3.50      inference(subtyping,[status(esa)],[c_7]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_174,plain,
% 22.63/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_20,c_19]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_473,plain,
% 22.63/3.50      ( k3_enumset1(sK1,sK1,sK0,sK2,sK0) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_380,c_174]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_725,plain,
% 22.63/3.50      ( k3_enumset1(sK0,sK1,sK1,sK0,sK2) != k3_enumset1(sK1,sK1,sK0,sK2,sK0) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_717,c_473]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_55734,plain,
% 22.63/3.50      ( k3_enumset1(sK1,sK0,sK0,sK0,sK2) != k3_enumset1(sK1,sK1,sK0,sK2,sK0) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_55320,c_725]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_195,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_24,c_25]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_500,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38),k1_tarski(X0_38))),k1_tarski(X0_38))) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_195,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_523,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X1_38,X1_38,X2_38) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_500,c_22,c_25]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_964,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X1_38,X2_38,X2_38) = k3_enumset1(X0_38,X2_38,X2_38,X2_38,X1_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_770,c_523]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_942,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X1_38,X2_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_770,c_769]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_2338,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X0_38,X1_38,X1_38,X2_38) = k3_enumset1(X0_38,X2_38,X2_38,X1_38,X1_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_964,c_942]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_319,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X2_38,X3_38,X4_38,X5_38),k1_tarski(X0_38))) = k6_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_21,c_20]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_22217,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X1_38,X1_38,X2_38,X2_38,X3_38),k1_tarski(X0_38))) = k6_enumset1(X0_38,X0_38,X0_38,X1_38,X3_38,X3_38,X2_38,X2_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_2338,c_319]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_812,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X3_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_769,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_253,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k5_xboole_0(k1_tarski(X5_38),k4_xboole_0(k1_tarski(X5_38),k1_tarski(X5_38))),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38,X5_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_197,c_20]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_269,plain,
% 22.63/3.50      ( k5_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k4_xboole_0(k1_tarski(X5_38),k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38,X5_38,X5_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_253,c_188]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_7387,plain,
% 22.63/3.50      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))),k4_xboole_0(k1_tarski(X4_38),k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38),k1_tarski(X0_38))))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X3_38,X4_38,X4_38) ),
% 22.63/3.50      inference(superposition,[status(thm)],[c_812,c_269]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_7551,plain,
% 22.63/3.50      ( k5_xboole_0(k1_tarski(X0_38),k4_xboole_0(k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38),k1_tarski(X0_38))) = k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X3_38,X4_38,X4_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_7387,c_22,c_23]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_7552,plain,
% 22.63/3.50      ( k6_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X3_38,X4_38,X4_38) = k3_enumset1(X0_38,X1_38,X2_38,X3_38,X4_38) ),
% 22.63/3.50      inference(light_normalisation,[status(thm)],[c_7551,c_22]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_22418,plain,
% 22.63/3.50      ( k3_enumset1(X0_38,X1_38,X2_38,X2_38,X3_38) = k3_enumset1(X0_38,X0_38,X1_38,X3_38,X2_38) ),
% 22.63/3.50      inference(demodulation,[status(thm)],[c_22217,c_25,c_7552]) ).
% 22.63/3.50  
% 22.63/3.50  cnf(c_57048,plain,
% 22.63/3.50      ( $false ),
% 22.63/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_55734,c_22418]) ).
% 22.63/3.50  
% 22.63/3.50  
% 22.63/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 22.63/3.50  
% 22.63/3.50  ------                               Statistics
% 22.63/3.50  
% 22.63/3.50  ------ Selected
% 22.63/3.50  
% 22.63/3.50  total_time:                             2.692
% 22.63/3.50  
%------------------------------------------------------------------------------
