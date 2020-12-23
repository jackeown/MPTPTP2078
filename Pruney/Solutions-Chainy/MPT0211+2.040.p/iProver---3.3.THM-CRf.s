%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:29 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  177 (82793 expanded)
%              Number of clauses        :  125 (21854 expanded)
%              Number of leaves         :   19 (26967 expanded)
%              Depth                    :   31
%              Number of atoms          :  178 (82794 expanded)
%              Number of equality atoms :  177 (82793 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f28,f39,f39])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f33,f45,f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f29,f26,f28])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(definition_unfolding,[],[f32,f45,f45])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f31,f28,f39])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f46,f43])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) ),
    inference(definition_unfolding,[],[f36,f28,f39,f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0)),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0))) ),
    inference(definition_unfolding,[],[f34,f45,f45])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f35,f28,f47,f45])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f21])).

fof(f23,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f44,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f44,f28,f39,f39])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_33,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_42,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1])).

cnf(c_36,plain,
    ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),X2_35) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,X2_35)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_37,plain,
    ( k5_xboole_0(X0_35,X1_35) = k5_xboole_0(X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_64,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,X2_35)) = k5_xboole_0(X1_35,k5_xboole_0(X2_35,X0_35)) ),
    inference(superposition,[status(thm)],[c_36,c_37])).

cnf(c_236,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X2_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X1_36),k1_enumset1(X0_36,X0_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_42,c_64])).

cnf(c_250,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_42,c_64])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_35,plain,
    ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_40,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(theory_normalisation,[status(thm)],[c_35,c_2,c_1])).

cnf(c_67,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) = k5_xboole_0(X1_35,k5_xboole_0(k3_xboole_0(X0_35,X1_35),X0_35)) ),
    inference(superposition,[status(thm)],[c_64,c_40])).

cnf(c_62,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,X2_35)) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,X2_35)) ),
    inference(superposition,[status(thm)],[c_36,c_37])).

cnf(c_127,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(k3_xboole_0(X1_35,X0_35),X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) ),
    inference(superposition,[status(thm)],[c_67,c_62])).

cnf(c_254,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)))) ),
    inference(superposition,[status(thm)],[c_42,c_40])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_46,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1])).

cnf(c_210,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X1_36,X0_36,X3_36) ),
    inference(superposition,[status(thm)],[c_41,c_46])).

cnf(c_260,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X1_36,X0_36) ),
    inference(light_normalisation,[status(thm)],[c_254,c_210])).

cnf(c_261,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X1_36,X0_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_260,c_42])).

cnf(c_313,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)),k1_enumset1(X2_36,X2_36,X3_36))) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_250,c_127,c_261])).

cnf(c_240,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_42,c_40])).

cnf(c_322,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X3_36,X1_36) ),
    inference(light_normalisation,[status(thm)],[c_240,c_210])).

cnf(c_324,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
    inference(demodulation,[status(thm)],[c_236,c_313,c_322])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_38,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_39,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(theory_normalisation,[status(thm)],[c_38,c_2,c_1])).

cnf(c_173,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_46,c_39])).

cnf(c_1219,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X0_36,X2_36) = k1_enumset1(X0_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_324,c_173])).

cnf(c_1226,plain,
    ( k1_enumset1(X0_36,X1_36,X0_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_1219,c_173])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_45,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36)))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_30,c_2,c_1])).

cnf(c_84,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k5_xboole_0(X2_35,k3_xboole_0(X0_35,X2_35)))) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,k5_xboole_0(X2_35,k3_xboole_0(X2_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_40,c_62])).

cnf(c_1524,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X0_36,X1_36))))) ),
    inference(superposition,[status(thm)],[c_45,c_84])).

cnf(c_1526,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X1_36))))) ),
    inference(superposition,[status(thm)],[c_45,c_84])).

cnf(c_78,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k5_xboole_0(X2_35,k3_xboole_0(X2_35,X1_35)))) = k5_xboole_0(X1_35,k5_xboole_0(k5_xboole_0(X2_35,k3_xboole_0(X1_35,X2_35)),X0_35)) ),
    inference(superposition,[status(thm)],[c_40,c_64])).

cnf(c_958,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))),X0_35)) ),
    inference(superposition,[status(thm)],[c_45,c_78])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0)),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_43,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_32,c_2,c_1])).

cnf(c_76,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35)),X2_35)) = k5_xboole_0(k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))),X2_35) ),
    inference(superposition,[status(thm)],[c_40,c_36])).

cnf(c_857,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))),X0_35)) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k1_enumset1(X1_36,X1_36,X0_36)))),X0_35) ),
    inference(superposition,[status(thm)],[c_43,c_76])).

cnf(c_87,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35)),X2_35)) = k5_xboole_0(k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))),X2_35) ),
    inference(superposition,[status(thm)],[c_40,c_36])).

cnf(c_253,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X1_36)))) = k1_enumset1(X1_36,X2_36,X0_36) ),
    inference(superposition,[status(thm)],[c_42,c_39])).

cnf(c_247,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))),X0_35)) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))))) ),
    inference(superposition,[status(thm)],[c_42,c_64])).

cnf(c_314,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))),X0_35)) = k5_xboole_0(X0_35,k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X3_36,X1_36)) ),
    inference(demodulation,[status(thm)],[c_247,c_261])).

cnf(c_929,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))),X0_35)) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
    inference(demodulation,[status(thm)],[c_857,c_87,c_253,c_314])).

cnf(c_1026,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
    inference(light_normalisation,[status(thm)],[c_958,c_929])).

cnf(c_1593,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
    inference(light_normalisation,[status(thm)],[c_1526,c_1026])).

cnf(c_1596,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
    inference(demodulation,[status(thm)],[c_1524,c_1593])).

cnf(c_1264,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X1_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1226,c_39])).

cnf(c_1597,plain,
    ( k5_xboole_0(X0_35,k1_enumset1(X0_36,X1_36,X0_36)) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
    inference(demodulation,[status(thm)],[c_1596,c_1264])).

cnf(c_3447,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) = k5_xboole_0(X0_35,k1_enumset1(X0_36,X0_36,X1_36)) ),
    inference(superposition,[status(thm)],[c_1226,c_1597])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_44,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1])).

cnf(c_5445,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))),k1_enumset1(X1_36,X1_36,X2_36)) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_3447,c_44])).

cnf(c_5447,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36))),k1_enumset1(X2_36,X2_36,X3_36)) = k5_enumset1(X2_36,X2_36,X2_36,X3_36,X3_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_3447,c_46])).

cnf(c_5578,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) ),
    inference(demodulation,[status(thm)],[c_5445,c_5447])).

cnf(c_1240,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_1226,c_44])).

cnf(c_1242,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1226,c_46])).

cnf(c_1266,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X2_36) ),
    inference(demodulation,[status(thm)],[c_1240,c_1242])).

cnf(c_702,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_44,c_43])).

cnf(c_739,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X2_36,X1_36,X0_36) ),
    inference(light_normalisation,[status(thm)],[c_702,c_39])).

cnf(c_1267,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X2_36) = k1_enumset1(X2_36,X1_36,X0_36) ),
    inference(light_normalisation,[status(thm)],[c_1266,c_739])).

cnf(c_1283,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X0_36,X0_36) ),
    inference(superposition,[status(thm)],[c_1267,c_173])).

cnf(c_1297,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_1283,c_44])).

cnf(c_1299,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1283,c_46])).

cnf(c_1303,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) ),
    inference(demodulation,[status(thm)],[c_1297,c_1299])).

cnf(c_780,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_45,c_39])).

cnf(c_1304,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(light_normalisation,[status(thm)],[c_1303,c_780])).

cnf(c_2172,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_1304,c_173])).

cnf(c_2181,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_2172,c_44])).

cnf(c_2183,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_2172,c_46])).

cnf(c_2191,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_2172,c_44])).

cnf(c_2212,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_2172,c_43])).

cnf(c_2219,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X3_36,X3_36,X1_36,X0_36) ),
    inference(light_normalisation,[status(thm)],[c_2212,c_1299])).

cnf(c_2208,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X3_36)))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_2172,c_44])).

cnf(c_2214,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X3_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_2172,c_43])).

cnf(c_810,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_45,c_46])).

cnf(c_1234,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1226,c_46])).

cnf(c_2218,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X3_36)))) = k5_enumset1(X3_36,X3_36,X3_36,X2_36,X3_36,X1_36,X0_36) ),
    inference(demodulation,[status(thm)],[c_2214,c_810,c_1234])).

cnf(c_2220,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)))) = k5_enumset1(X3_36,X3_36,X3_36,X2_36,X3_36,X1_36,X0_36) ),
    inference(demodulation,[status(thm)],[c_2208,c_2218])).

cnf(c_2221,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X2_36,X2_36,X0_36,X0_36) ),
    inference(demodulation,[status(thm)],[c_2191,c_2219,c_2220])).

cnf(c_2171,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1304,c_46])).

cnf(c_2222,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) = k1_enumset1(X2_36,X0_36,X1_36) ),
    inference(light_normalisation,[status(thm)],[c_2221,c_2171])).

cnf(c_2223,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X2_36,X0_36,X1_36) ),
    inference(demodulation,[status(thm)],[c_2181,c_2183,c_2222])).

cnf(c_1521,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X1_36,X1_36,X1_36))))) ),
    inference(superposition,[status(thm)],[c_44,c_84])).

cnf(c_1600,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X1_36,X1_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
    inference(demodulation,[status(thm)],[c_1521,c_1593])).

cnf(c_1601,plain,
    ( k5_xboole_0(X0_35,k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36,X1_36)) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
    inference(demodulation,[status(thm)],[c_1600,c_1242])).

cnf(c_1285,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36,X2_36) = k1_enumset1(X1_36,X2_36,X0_36) ),
    inference(superposition,[status(thm)],[c_1267,c_324])).

cnf(c_1602,plain,
    ( k5_xboole_0(X0_35,k1_enumset1(X0_36,X0_36,X1_36)) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),X0_35) ),
    inference(demodulation,[status(thm)],[c_1601,c_1285])).

cnf(c_3632,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),X0_35) ),
    inference(superposition,[status(thm)],[c_37,c_1602])).

cnf(c_4574,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_3632,c_44])).

cnf(c_4575,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k1_enumset1(X0_36,X2_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_3632,c_45])).

cnf(c_2175,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X1_36,X0_36) ),
    inference(superposition,[status(thm)],[c_1304,c_1267])).

cnf(c_2229,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_1226,c_2175])).

cnf(c_2315,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_2229,c_45])).

cnf(c_1295,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_1283,c_45])).

cnf(c_1305,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_1295,c_1299])).

cnf(c_2199,plain,
    ( k1_enumset1(X0_36,X1_36,X0_36) = k1_enumset1(X0_36,X1_36,X1_36) ),
    inference(superposition,[status(thm)],[c_2172,c_1226])).

cnf(c_2295,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_2199,c_46])).

cnf(c_2344,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X2_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_2315,c_1305,c_2295])).

cnf(c_4769,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_4575,c_2344])).

cnf(c_4770,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X2_36,X2_36) ),
    inference(demodulation,[status(thm)],[c_4574,c_4769])).

cnf(c_4771,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) = k1_enumset1(X2_36,X1_36,X0_36) ),
    inference(light_normalisation,[status(thm)],[c_4770,c_2223])).

cnf(c_5579,plain,
    ( k1_enumset1(X0_36,X1_36,X2_36) = k1_enumset1(X0_36,X2_36,X1_36) ),
    inference(light_normalisation,[status(thm)],[c_5578,c_2223,c_4771])).

cnf(c_3771,plain,
    ( k1_enumset1(X0_36,X1_36,X2_36) = k1_enumset1(X1_36,X2_36,X0_36) ),
    inference(superposition,[status(thm)],[c_1304,c_2222])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_47,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_28,c_2,c_1])).

cnf(c_61,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_46,c_47])).

cnf(c_1213,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_324,c_61])).

cnf(c_2157,plain,
    ( k1_enumset1(sK0,sK2,sK1) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1285,c_1213])).

cnf(c_4902,plain,
    ( k1_enumset1(sK1,sK2,sK0) != k1_enumset1(sK0,sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_3771,c_2157])).

cnf(c_5039,plain,
    ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(superposition,[status(thm)],[c_3771,c_4902])).

cnf(c_5589,plain,
    ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_5579,c_5039])).

cnf(c_5590,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_5589])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:34:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.60/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/1.00  
% 2.60/1.00  ------  iProver source info
% 2.60/1.00  
% 2.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/1.00  git: non_committed_changes: false
% 2.60/1.00  git: last_make_outside_of_git: false
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options
% 2.60/1.00  
% 2.60/1.00  --out_options                           all
% 2.60/1.00  --tptp_safe_out                         true
% 2.60/1.00  --problem_path                          ""
% 2.60/1.00  --include_path                          ""
% 2.60/1.00  --clausifier                            res/vclausify_rel
% 2.60/1.00  --clausifier_options                    --mode clausify
% 2.60/1.00  --stdin                                 false
% 2.60/1.00  --stats_out                             all
% 2.60/1.00  
% 2.60/1.00  ------ General Options
% 2.60/1.00  
% 2.60/1.00  --fof                                   false
% 2.60/1.00  --time_out_real                         305.
% 2.60/1.00  --time_out_virtual                      -1.
% 2.60/1.00  --symbol_type_check                     false
% 2.60/1.00  --clausify_out                          false
% 2.60/1.00  --sig_cnt_out                           false
% 2.60/1.00  --trig_cnt_out                          false
% 2.60/1.00  --trig_cnt_out_tolerance                1.
% 2.60/1.00  --trig_cnt_out_sk_spl                   false
% 2.60/1.00  --abstr_cl_out                          false
% 2.60/1.00  
% 2.60/1.00  ------ Global Options
% 2.60/1.00  
% 2.60/1.00  --schedule                              default
% 2.60/1.00  --add_important_lit                     false
% 2.60/1.00  --prop_solver_per_cl                    1000
% 2.60/1.00  --min_unsat_core                        false
% 2.60/1.00  --soft_assumptions                      false
% 2.60/1.00  --soft_lemma_size                       3
% 2.60/1.00  --prop_impl_unit_size                   0
% 2.60/1.00  --prop_impl_unit                        []
% 2.60/1.00  --share_sel_clauses                     true
% 2.60/1.00  --reset_solvers                         false
% 2.60/1.00  --bc_imp_inh                            [conj_cone]
% 2.60/1.00  --conj_cone_tolerance                   3.
% 2.60/1.00  --extra_neg_conj                        none
% 2.60/1.00  --large_theory_mode                     true
% 2.60/1.00  --prolific_symb_bound                   200
% 2.60/1.00  --lt_threshold                          2000
% 2.60/1.00  --clause_weak_htbl                      true
% 2.60/1.00  --gc_record_bc_elim                     false
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing Options
% 2.60/1.00  
% 2.60/1.00  --preprocessing_flag                    true
% 2.60/1.00  --time_out_prep_mult                    0.1
% 2.60/1.00  --splitting_mode                        input
% 2.60/1.00  --splitting_grd                         true
% 2.60/1.00  --splitting_cvd                         false
% 2.60/1.00  --splitting_cvd_svl                     false
% 2.60/1.00  --splitting_nvd                         32
% 2.60/1.00  --sub_typing                            true
% 2.60/1.00  --prep_gs_sim                           true
% 2.60/1.00  --prep_unflatten                        true
% 2.60/1.00  --prep_res_sim                          true
% 2.60/1.00  --prep_upred                            true
% 2.60/1.00  --prep_sem_filter                       exhaustive
% 2.60/1.00  --prep_sem_filter_out                   false
% 2.60/1.00  --pred_elim                             true
% 2.60/1.00  --res_sim_input                         true
% 2.60/1.00  --eq_ax_congr_red                       true
% 2.60/1.00  --pure_diseq_elim                       true
% 2.60/1.00  --brand_transform                       false
% 2.60/1.00  --non_eq_to_eq                          false
% 2.60/1.00  --prep_def_merge                        true
% 2.60/1.00  --prep_def_merge_prop_impl              false
% 2.60/1.00  --prep_def_merge_mbd                    true
% 2.60/1.00  --prep_def_merge_tr_red                 false
% 2.60/1.00  --prep_def_merge_tr_cl                  false
% 2.60/1.00  --smt_preprocessing                     true
% 2.60/1.00  --smt_ac_axioms                         fast
% 2.60/1.00  --preprocessed_out                      false
% 2.60/1.00  --preprocessed_stats                    false
% 2.60/1.00  
% 2.60/1.00  ------ Abstraction refinement Options
% 2.60/1.00  
% 2.60/1.00  --abstr_ref                             []
% 2.60/1.00  --abstr_ref_prep                        false
% 2.60/1.00  --abstr_ref_until_sat                   false
% 2.60/1.00  --abstr_ref_sig_restrict                funpre
% 2.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.00  --abstr_ref_under                       []
% 2.60/1.00  
% 2.60/1.00  ------ SAT Options
% 2.60/1.00  
% 2.60/1.00  --sat_mode                              false
% 2.60/1.00  --sat_fm_restart_options                ""
% 2.60/1.00  --sat_gr_def                            false
% 2.60/1.00  --sat_epr_types                         true
% 2.60/1.00  --sat_non_cyclic_types                  false
% 2.60/1.00  --sat_finite_models                     false
% 2.60/1.00  --sat_fm_lemmas                         false
% 2.60/1.00  --sat_fm_prep                           false
% 2.60/1.00  --sat_fm_uc_incr                        true
% 2.60/1.00  --sat_out_model                         small
% 2.60/1.00  --sat_out_clauses                       false
% 2.60/1.00  
% 2.60/1.00  ------ QBF Options
% 2.60/1.00  
% 2.60/1.00  --qbf_mode                              false
% 2.60/1.00  --qbf_elim_univ                         false
% 2.60/1.00  --qbf_dom_inst                          none
% 2.60/1.00  --qbf_dom_pre_inst                      false
% 2.60/1.00  --qbf_sk_in                             false
% 2.60/1.00  --qbf_pred_elim                         true
% 2.60/1.00  --qbf_split                             512
% 2.60/1.00  
% 2.60/1.00  ------ BMC1 Options
% 2.60/1.00  
% 2.60/1.00  --bmc1_incremental                      false
% 2.60/1.00  --bmc1_axioms                           reachable_all
% 2.60/1.00  --bmc1_min_bound                        0
% 2.60/1.00  --bmc1_max_bound                        -1
% 2.60/1.00  --bmc1_max_bound_default                -1
% 2.60/1.00  --bmc1_symbol_reachability              true
% 2.60/1.00  --bmc1_property_lemmas                  false
% 2.60/1.00  --bmc1_k_induction                      false
% 2.60/1.00  --bmc1_non_equiv_states                 false
% 2.60/1.00  --bmc1_deadlock                         false
% 2.60/1.00  --bmc1_ucm                              false
% 2.60/1.00  --bmc1_add_unsat_core                   none
% 2.60/1.00  --bmc1_unsat_core_children              false
% 2.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.00  --bmc1_out_stat                         full
% 2.60/1.00  --bmc1_ground_init                      false
% 2.60/1.00  --bmc1_pre_inst_next_state              false
% 2.60/1.00  --bmc1_pre_inst_state                   false
% 2.60/1.00  --bmc1_pre_inst_reach_state             false
% 2.60/1.00  --bmc1_out_unsat_core                   false
% 2.60/1.00  --bmc1_aig_witness_out                  false
% 2.60/1.00  --bmc1_verbose                          false
% 2.60/1.00  --bmc1_dump_clauses_tptp                false
% 2.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.00  --bmc1_dump_file                        -
% 2.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.00  --bmc1_ucm_extend_mode                  1
% 2.60/1.00  --bmc1_ucm_init_mode                    2
% 2.60/1.00  --bmc1_ucm_cone_mode                    none
% 2.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.00  --bmc1_ucm_relax_model                  4
% 2.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.00  --bmc1_ucm_layered_model                none
% 2.60/1.00  --bmc1_ucm_max_lemma_size               10
% 2.60/1.00  
% 2.60/1.00  ------ AIG Options
% 2.60/1.00  
% 2.60/1.00  --aig_mode                              false
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation Options
% 2.60/1.00  
% 2.60/1.00  --instantiation_flag                    true
% 2.60/1.00  --inst_sos_flag                         false
% 2.60/1.00  --inst_sos_phase                        true
% 2.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel_side                     num_symb
% 2.60/1.00  --inst_solver_per_active                1400
% 2.60/1.00  --inst_solver_calls_frac                1.
% 2.60/1.00  --inst_passive_queue_type               priority_queues
% 2.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.00  --inst_passive_queues_freq              [25;2]
% 2.60/1.00  --inst_dismatching                      true
% 2.60/1.00  --inst_eager_unprocessed_to_passive     true
% 2.60/1.00  --inst_prop_sim_given                   true
% 2.60/1.00  --inst_prop_sim_new                     false
% 2.60/1.00  --inst_subs_new                         false
% 2.60/1.00  --inst_eq_res_simp                      false
% 2.60/1.00  --inst_subs_given                       false
% 2.60/1.00  --inst_orphan_elimination               true
% 2.60/1.00  --inst_learning_loop_flag               true
% 2.60/1.00  --inst_learning_start                   3000
% 2.60/1.00  --inst_learning_factor                  2
% 2.60/1.00  --inst_start_prop_sim_after_learn       3
% 2.60/1.00  --inst_sel_renew                        solver
% 2.60/1.00  --inst_lit_activity_flag                true
% 2.60/1.00  --inst_restr_to_given                   false
% 2.60/1.00  --inst_activity_threshold               500
% 2.60/1.00  --inst_out_proof                        true
% 2.60/1.00  
% 2.60/1.00  ------ Resolution Options
% 2.60/1.00  
% 2.60/1.00  --resolution_flag                       true
% 2.60/1.00  --res_lit_sel                           adaptive
% 2.60/1.00  --res_lit_sel_side                      none
% 2.60/1.00  --res_ordering                          kbo
% 2.60/1.00  --res_to_prop_solver                    active
% 2.60/1.00  --res_prop_simpl_new                    false
% 2.60/1.00  --res_prop_simpl_given                  true
% 2.60/1.00  --res_passive_queue_type                priority_queues
% 2.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.00  --res_passive_queues_freq               [15;5]
% 2.60/1.00  --res_forward_subs                      full
% 2.60/1.00  --res_backward_subs                     full
% 2.60/1.00  --res_forward_subs_resolution           true
% 2.60/1.00  --res_backward_subs_resolution          true
% 2.60/1.00  --res_orphan_elimination                true
% 2.60/1.00  --res_time_limit                        2.
% 2.60/1.00  --res_out_proof                         true
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Options
% 2.60/1.00  
% 2.60/1.00  --superposition_flag                    true
% 2.60/1.00  --sup_passive_queue_type                priority_queues
% 2.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.00  --demod_completeness_check              fast
% 2.60/1.00  --demod_use_ground                      true
% 2.60/1.00  --sup_to_prop_solver                    passive
% 2.60/1.00  --sup_prop_simpl_new                    true
% 2.60/1.00  --sup_prop_simpl_given                  true
% 2.60/1.00  --sup_fun_splitting                     false
% 2.60/1.00  --sup_smt_interval                      50000
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Simplification Setup
% 2.60/1.00  
% 2.60/1.00  --sup_indices_passive                   []
% 2.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_full_bw                           [BwDemod]
% 2.60/1.00  --sup_immed_triv                        [TrivRules]
% 2.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_immed_bw_main                     []
% 2.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  
% 2.60/1.00  ------ Combination Options
% 2.60/1.00  
% 2.60/1.00  --comb_res_mult                         3
% 2.60/1.00  --comb_sup_mult                         2
% 2.60/1.00  --comb_inst_mult                        10
% 2.60/1.00  
% 2.60/1.00  ------ Debug Options
% 2.60/1.00  
% 2.60/1.00  --dbg_backtrace                         false
% 2.60/1.00  --dbg_dump_prop_clauses                 false
% 2.60/1.00  --dbg_dump_prop_clauses_file            -
% 2.60/1.00  --dbg_out_stat                          false
% 2.60/1.00  ------ Parsing...
% 2.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.60/1.00  ------ Proving...
% 2.60/1.00  ------ Problem Properties 
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  clauses                                 11
% 2.60/1.00  conjectures                             1
% 2.60/1.00  EPR                                     0
% 2.60/1.00  Horn                                    11
% 2.60/1.00  unary                                   11
% 2.60/1.00  binary                                  0
% 2.60/1.00  lits                                    11
% 2.60/1.00  lits eq                                 11
% 2.60/1.00  fd_pure                                 0
% 2.60/1.00  fd_pseudo                               0
% 2.60/1.00  fd_cond                                 0
% 2.60/1.00  fd_pseudo_cond                          0
% 2.60/1.00  AC symbols                              1
% 2.60/1.00  
% 2.60/1.00  ------ Schedule UEQ
% 2.60/1.00  
% 2.60/1.00  ------ pure equality problem: resolution off 
% 2.60/1.00  
% 2.60/1.00  ------ Option_UEQ Time Limit: Unbounded
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  Current options:
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options
% 2.60/1.00  
% 2.60/1.00  --out_options                           all
% 2.60/1.00  --tptp_safe_out                         true
% 2.60/1.00  --problem_path                          ""
% 2.60/1.00  --include_path                          ""
% 2.60/1.00  --clausifier                            res/vclausify_rel
% 2.60/1.00  --clausifier_options                    --mode clausify
% 2.60/1.00  --stdin                                 false
% 2.60/1.00  --stats_out                             all
% 2.60/1.00  
% 2.60/1.00  ------ General Options
% 2.60/1.00  
% 2.60/1.00  --fof                                   false
% 2.60/1.00  --time_out_real                         305.
% 2.60/1.00  --time_out_virtual                      -1.
% 2.60/1.00  --symbol_type_check                     false
% 2.60/1.00  --clausify_out                          false
% 2.60/1.00  --sig_cnt_out                           false
% 2.60/1.00  --trig_cnt_out                          false
% 2.60/1.00  --trig_cnt_out_tolerance                1.
% 2.60/1.00  --trig_cnt_out_sk_spl                   false
% 2.60/1.00  --abstr_cl_out                          false
% 2.60/1.00  
% 2.60/1.00  ------ Global Options
% 2.60/1.00  
% 2.60/1.00  --schedule                              default
% 2.60/1.00  --add_important_lit                     false
% 2.60/1.00  --prop_solver_per_cl                    1000
% 2.60/1.00  --min_unsat_core                        false
% 2.60/1.00  --soft_assumptions                      false
% 2.60/1.00  --soft_lemma_size                       3
% 2.60/1.00  --prop_impl_unit_size                   0
% 2.60/1.00  --prop_impl_unit                        []
% 2.60/1.00  --share_sel_clauses                     true
% 2.60/1.00  --reset_solvers                         false
% 2.60/1.00  --bc_imp_inh                            [conj_cone]
% 2.60/1.00  --conj_cone_tolerance                   3.
% 2.60/1.00  --extra_neg_conj                        none
% 2.60/1.00  --large_theory_mode                     true
% 2.60/1.00  --prolific_symb_bound                   200
% 2.60/1.00  --lt_threshold                          2000
% 2.60/1.00  --clause_weak_htbl                      true
% 2.60/1.00  --gc_record_bc_elim                     false
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing Options
% 2.60/1.00  
% 2.60/1.00  --preprocessing_flag                    true
% 2.60/1.00  --time_out_prep_mult                    0.1
% 2.60/1.00  --splitting_mode                        input
% 2.60/1.00  --splitting_grd                         true
% 2.60/1.00  --splitting_cvd                         false
% 2.60/1.00  --splitting_cvd_svl                     false
% 2.60/1.00  --splitting_nvd                         32
% 2.60/1.00  --sub_typing                            true
% 2.60/1.00  --prep_gs_sim                           true
% 2.60/1.00  --prep_unflatten                        true
% 2.60/1.00  --prep_res_sim                          true
% 2.60/1.00  --prep_upred                            true
% 2.60/1.00  --prep_sem_filter                       exhaustive
% 2.60/1.00  --prep_sem_filter_out                   false
% 2.60/1.00  --pred_elim                             true
% 2.60/1.00  --res_sim_input                         true
% 2.60/1.00  --eq_ax_congr_red                       true
% 2.60/1.00  --pure_diseq_elim                       true
% 2.60/1.00  --brand_transform                       false
% 2.60/1.00  --non_eq_to_eq                          false
% 2.60/1.00  --prep_def_merge                        true
% 2.60/1.00  --prep_def_merge_prop_impl              false
% 2.60/1.00  --prep_def_merge_mbd                    true
% 2.60/1.00  --prep_def_merge_tr_red                 false
% 2.60/1.00  --prep_def_merge_tr_cl                  false
% 2.60/1.00  --smt_preprocessing                     true
% 2.60/1.00  --smt_ac_axioms                         fast
% 2.60/1.00  --preprocessed_out                      false
% 2.60/1.00  --preprocessed_stats                    false
% 2.60/1.00  
% 2.60/1.00  ------ Abstraction refinement Options
% 2.60/1.00  
% 2.60/1.00  --abstr_ref                             []
% 2.60/1.00  --abstr_ref_prep                        false
% 2.60/1.00  --abstr_ref_until_sat                   false
% 2.60/1.00  --abstr_ref_sig_restrict                funpre
% 2.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.00  --abstr_ref_under                       []
% 2.60/1.00  
% 2.60/1.00  ------ SAT Options
% 2.60/1.00  
% 2.60/1.00  --sat_mode                              false
% 2.60/1.00  --sat_fm_restart_options                ""
% 2.60/1.00  --sat_gr_def                            false
% 2.60/1.00  --sat_epr_types                         true
% 2.60/1.00  --sat_non_cyclic_types                  false
% 2.60/1.00  --sat_finite_models                     false
% 2.60/1.00  --sat_fm_lemmas                         false
% 2.60/1.00  --sat_fm_prep                           false
% 2.60/1.00  --sat_fm_uc_incr                        true
% 2.60/1.00  --sat_out_model                         small
% 2.60/1.00  --sat_out_clauses                       false
% 2.60/1.00  
% 2.60/1.00  ------ QBF Options
% 2.60/1.00  
% 2.60/1.00  --qbf_mode                              false
% 2.60/1.00  --qbf_elim_univ                         false
% 2.60/1.00  --qbf_dom_inst                          none
% 2.60/1.00  --qbf_dom_pre_inst                      false
% 2.60/1.00  --qbf_sk_in                             false
% 2.60/1.00  --qbf_pred_elim                         true
% 2.60/1.00  --qbf_split                             512
% 2.60/1.00  
% 2.60/1.00  ------ BMC1 Options
% 2.60/1.00  
% 2.60/1.00  --bmc1_incremental                      false
% 2.60/1.00  --bmc1_axioms                           reachable_all
% 2.60/1.00  --bmc1_min_bound                        0
% 2.60/1.00  --bmc1_max_bound                        -1
% 2.60/1.00  --bmc1_max_bound_default                -1
% 2.60/1.00  --bmc1_symbol_reachability              true
% 2.60/1.00  --bmc1_property_lemmas                  false
% 2.60/1.00  --bmc1_k_induction                      false
% 2.60/1.00  --bmc1_non_equiv_states                 false
% 2.60/1.00  --bmc1_deadlock                         false
% 2.60/1.00  --bmc1_ucm                              false
% 2.60/1.00  --bmc1_add_unsat_core                   none
% 2.60/1.00  --bmc1_unsat_core_children              false
% 2.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.00  --bmc1_out_stat                         full
% 2.60/1.00  --bmc1_ground_init                      false
% 2.60/1.00  --bmc1_pre_inst_next_state              false
% 2.60/1.00  --bmc1_pre_inst_state                   false
% 2.60/1.00  --bmc1_pre_inst_reach_state             false
% 2.60/1.00  --bmc1_out_unsat_core                   false
% 2.60/1.00  --bmc1_aig_witness_out                  false
% 2.60/1.00  --bmc1_verbose                          false
% 2.60/1.00  --bmc1_dump_clauses_tptp                false
% 2.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.00  --bmc1_dump_file                        -
% 2.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.00  --bmc1_ucm_extend_mode                  1
% 2.60/1.00  --bmc1_ucm_init_mode                    2
% 2.60/1.00  --bmc1_ucm_cone_mode                    none
% 2.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.00  --bmc1_ucm_relax_model                  4
% 2.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.00  --bmc1_ucm_layered_model                none
% 2.60/1.00  --bmc1_ucm_max_lemma_size               10
% 2.60/1.00  
% 2.60/1.00  ------ AIG Options
% 2.60/1.00  
% 2.60/1.00  --aig_mode                              false
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation Options
% 2.60/1.00  
% 2.60/1.00  --instantiation_flag                    false
% 2.60/1.00  --inst_sos_flag                         false
% 2.60/1.00  --inst_sos_phase                        true
% 2.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel_side                     num_symb
% 2.60/1.00  --inst_solver_per_active                1400
% 2.60/1.00  --inst_solver_calls_frac                1.
% 2.60/1.00  --inst_passive_queue_type               priority_queues
% 2.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.00  --inst_passive_queues_freq              [25;2]
% 2.60/1.00  --inst_dismatching                      true
% 2.60/1.00  --inst_eager_unprocessed_to_passive     true
% 2.60/1.00  --inst_prop_sim_given                   true
% 2.60/1.00  --inst_prop_sim_new                     false
% 2.60/1.00  --inst_subs_new                         false
% 2.60/1.00  --inst_eq_res_simp                      false
% 2.60/1.00  --inst_subs_given                       false
% 2.60/1.00  --inst_orphan_elimination               true
% 2.60/1.00  --inst_learning_loop_flag               true
% 2.60/1.00  --inst_learning_start                   3000
% 2.60/1.00  --inst_learning_factor                  2
% 2.60/1.00  --inst_start_prop_sim_after_learn       3
% 2.60/1.00  --inst_sel_renew                        solver
% 2.60/1.00  --inst_lit_activity_flag                true
% 2.60/1.00  --inst_restr_to_given                   false
% 2.60/1.00  --inst_activity_threshold               500
% 2.60/1.00  --inst_out_proof                        true
% 2.60/1.00  
% 2.60/1.00  ------ Resolution Options
% 2.60/1.00  
% 2.60/1.00  --resolution_flag                       false
% 2.60/1.00  --res_lit_sel                           adaptive
% 2.60/1.00  --res_lit_sel_side                      none
% 2.60/1.00  --res_ordering                          kbo
% 2.60/1.00  --res_to_prop_solver                    active
% 2.60/1.00  --res_prop_simpl_new                    false
% 2.60/1.00  --res_prop_simpl_given                  true
% 2.60/1.00  --res_passive_queue_type                priority_queues
% 2.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.00  --res_passive_queues_freq               [15;5]
% 2.60/1.00  --res_forward_subs                      full
% 2.60/1.00  --res_backward_subs                     full
% 2.60/1.00  --res_forward_subs_resolution           true
% 2.60/1.00  --res_backward_subs_resolution          true
% 2.60/1.00  --res_orphan_elimination                true
% 2.60/1.00  --res_time_limit                        2.
% 2.60/1.00  --res_out_proof                         true
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Options
% 2.60/1.00  
% 2.60/1.00  --superposition_flag                    true
% 2.60/1.00  --sup_passive_queue_type                priority_queues
% 2.60/1.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.00  --demod_completeness_check              fast
% 2.60/1.00  --demod_use_ground                      true
% 2.60/1.00  --sup_to_prop_solver                    active
% 2.60/1.00  --sup_prop_simpl_new                    false
% 2.60/1.00  --sup_prop_simpl_given                  false
% 2.60/1.00  --sup_fun_splitting                     true
% 2.60/1.00  --sup_smt_interval                      10000
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Simplification Setup
% 2.60/1.00  
% 2.60/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.60/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_full_triv                         [TrivRules]
% 2.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.60/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.60/1.00  --sup_immed_triv                        [TrivRules]
% 2.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_bw_main                     []
% 2.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.60/1.00  
% 2.60/1.00  ------ Combination Options
% 2.60/1.00  
% 2.60/1.00  --comb_res_mult                         1
% 2.60/1.00  --comb_sup_mult                         1
% 2.60/1.00  --comb_inst_mult                        1000000
% 2.60/1.00  
% 2.60/1.00  ------ Debug Options
% 2.60/1.00  
% 2.60/1.00  --dbg_backtrace                         false
% 2.60/1.00  --dbg_dump_prop_clauses                 false
% 2.60/1.00  --dbg_dump_prop_clauses_file            -
% 2.60/1.00  --dbg_out_stat                          false
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ Proving...
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS status Theorem for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00   Resolution empty clause
% 2.60/1.00  
% 2.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  fof(f9,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f33,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f9])).
% 2.60/1.00  
% 2.60/1.00  fof(f6,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f30,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f6])).
% 2.60/1.00  
% 2.60/1.00  fof(f4,axiom,(
% 2.60/1.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f28,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f4])).
% 2.60/1.00  
% 2.60/1.00  fof(f15,axiom,(
% 2.60/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f39,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f15])).
% 2.60/1.00  
% 2.60/1.00  fof(f45,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f30,f28,f39,f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f52,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f33,f45,f45])).
% 2.60/1.00  
% 2.60/1.00  fof(f3,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f27,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f3])).
% 2.60/1.00  
% 2.60/1.00  fof(f1,axiom,(
% 2.60/1.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f25,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f1])).
% 2.60/1.00  
% 2.60/1.00  fof(f5,axiom,(
% 2.60/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f29,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f5])).
% 2.60/1.00  
% 2.60/1.00  fof(f2,axiom,(
% 2.60/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f26,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f2])).
% 2.60/1.00  
% 2.60/1.00  fof(f50,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f29,f26,f28])).
% 2.60/1.00  
% 2.60/1.00  fof(f8,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f32,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f8])).
% 2.60/1.00  
% 2.60/1.00  fof(f51,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f32,f45,f45])).
% 2.60/1.00  
% 2.60/1.00  fof(f18,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f42,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f18])).
% 2.60/1.00  
% 2.60/1.00  fof(f7,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f31,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f7])).
% 2.60/1.00  
% 2.60/1.00  fof(f46,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f31,f28,f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f19,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f43,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f19])).
% 2.60/1.00  
% 2.60/1.00  fof(f57,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f42,f46,f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f16,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f40,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f16])).
% 2.60/1.00  
% 2.60/1.00  fof(f49,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f40,f45])).
% 2.60/1.00  
% 2.60/1.00  fof(f12,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f36,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f12])).
% 2.60/1.00  
% 2.60/1.00  fof(f55,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f36,f28,f39,f46])).
% 2.60/1.00  
% 2.60/1.00  fof(f10,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f34,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f10])).
% 2.60/1.00  
% 2.60/1.00  fof(f53,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0)),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0)))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f34,f45,f45])).
% 2.60/1.00  
% 2.60/1.00  fof(f11,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f35,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f11])).
% 2.60/1.00  
% 2.60/1.00  fof(f14,axiom,(
% 2.60/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f38,plain,(
% 2.60/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f14])).
% 2.60/1.00  
% 2.60/1.00  fof(f47,plain,(
% 2.60/1.00    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f38,f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f54,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f35,f28,f47,f45])).
% 2.60/1.00  
% 2.60/1.00  fof(f20,conjecture,(
% 2.60/1.00    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f21,negated_conjecture,(
% 2.60/1.00    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.60/1.00    inference(negated_conjecture,[],[f20])).
% 2.60/1.00  
% 2.60/1.00  fof(f22,plain,(
% 2.60/1.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.60/1.00    inference(ennf_transformation,[],[f21])).
% 2.60/1.00  
% 2.60/1.00  fof(f23,plain,(
% 2.60/1.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f24,plain,(
% 2.60/1.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 2.60/1.00  
% 2.60/1.00  fof(f44,plain,(
% 2.60/1.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.60/1.01    inference(cnf_transformation,[],[f24])).
% 2.60/1.01  
% 2.60/1.01  fof(f58,plain,(
% 2.60/1.01    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.60/1.01    inference(definition_unfolding,[],[f44,f28,f39,f39])).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_33,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.60/1.01      inference(cnf_transformation,[],[f27]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1,plain,
% 2.60/1.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.60/1.01      inference(cnf_transformation,[],[f25]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_42,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_36,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),X2_35) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,X2_35)) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_37,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,X1_35) = k5_xboole_0(X1_35,X0_35) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_64,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,X2_35)) = k5_xboole_0(X1_35,k5_xboole_0(X2_35,X0_35)) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_36,c_37]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_236,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X2_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X1_36),k1_enumset1(X0_36,X0_36,X2_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_42,c_64]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_250,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_42,c_64]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_35,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_40,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_35,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_67,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) = k5_xboole_0(X1_35,k5_xboole_0(k3_xboole_0(X0_35,X1_35),X0_35)) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_64,c_40]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_62,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,X2_35)) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,X2_35)) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_36,c_37]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_127,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(k3_xboole_0(X1_35,X0_35),X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_67,c_62]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_254,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_42,c_40]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_34,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_41,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_10,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
% 2.60/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_29,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_46,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_210,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X1_36,X0_36,X3_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_41,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_260,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X1_36,X0_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_254,c_210]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_261,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X1_36,X0_36,X3_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_260,c_42]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_313,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)),k1_enumset1(X2_36,X2_36,X3_36))) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36,X3_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_250,c_127,c_261]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_240,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_42,c_40]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_322,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X3_36,X1_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_240,c_210]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_324,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_236,c_313,c_322]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_0,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.60/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_38,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_39,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_38,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_173,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_46,c_39]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1219,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X0_36,X2_36) = k1_enumset1(X0_36,X2_36,X1_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_324,c_173]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1226,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X0_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1219,c_173]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_8,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_30,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36))) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_45,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36)))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X4_36)))) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_30,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_84,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k5_xboole_0(X2_35,k3_xboole_0(X0_35,X2_35)))) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,k5_xboole_0(X2_35,k3_xboole_0(X2_35,X0_35)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_40,c_62]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1524,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X0_36,X1_36))))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_45,c_84]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1526,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X1_36))))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_45,c_84]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_78,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k5_xboole_0(X2_35,k3_xboole_0(X2_35,X1_35)))) = k5_xboole_0(X1_35,k5_xboole_0(k5_xboole_0(X2_35,k3_xboole_0(X1_35,X2_35)),X0_35)) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_40,c_64]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_958,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))),X0_35)) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_45,c_78]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0)),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_32,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36))) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_43,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_32,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_76,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35)),X2_35)) = k5_xboole_0(k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))),X2_35) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_40,c_36]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_857,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))),X0_35)) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k1_enumset1(X1_36,X1_36,X0_36)))),X0_35) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_43,c_76]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_87,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35)),X2_35)) = k5_xboole_0(k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))),X2_35) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_40,c_36]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_253,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X1_36)))) = k1_enumset1(X1_36,X2_36,X0_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_42,c_39]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_247,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))),X0_35)) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_42,c_64]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_314,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))),X0_35)) = k5_xboole_0(X0_35,k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X3_36,X1_36)) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_247,c_261]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_929,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))),X0_35)) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_857,c_87,c_253,c_314]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1026,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_958,c_929]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1593,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_1526,c_1026]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1596,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X0_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1524,c_1593]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1264,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X1_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1226,c_39]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1597,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k1_enumset1(X0_36,X1_36,X0_36)) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1596,c_1264]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3447,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) = k5_xboole_0(X0_35,k1_enumset1(X0_36,X0_36,X1_36)) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1226,c_1597]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_7,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
% 2.60/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_31,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_44,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5445,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))),k1_enumset1(X1_36,X1_36,X2_36)) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_3447,c_44]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5447,plain,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36))),k1_enumset1(X2_36,X2_36,X3_36)) = k5_enumset1(X2_36,X2_36,X2_36,X3_36,X3_36,X0_36,X1_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_3447,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5578,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_5445,c_5447]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1240,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1226,c_44]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1242,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1226,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1266,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X2_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1240,c_1242]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_702,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_44,c_43]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_739,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X2_36,X1_36,X0_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_702,c_39]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1267,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X2_36) = k1_enumset1(X2_36,X1_36,X0_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_1266,c_739]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1283,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X0_36,X0_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1267,c_173]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1297,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X2_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1283,c_44]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1299,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X2_36,X3_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1283,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1303,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1297,c_1299]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_780,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_45,c_39]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1304,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_1303,c_780]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2172,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1304,c_173]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2181,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2172,c_44]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2183,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2172,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2191,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2172,c_44]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2212,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2172,c_43]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2219,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X2_36,X2_36,X2_36,X3_36,X3_36,X1_36,X0_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_2212,c_1299]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2208,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X3_36)))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2172,c_44]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2214,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X3_36)))) = k5_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X2_36),k1_enumset1(X1_36,X1_36,X0_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2172,c_43]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_810,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X4_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_45,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1234,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36,X2_36,X3_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1226,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2218,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X3_36,X3_36)))) = k5_enumset1(X3_36,X3_36,X3_36,X2_36,X3_36,X1_36,X0_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_2214,c_810,c_1234]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2220,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)))) = k5_enumset1(X3_36,X3_36,X3_36,X2_36,X3_36,X1_36,X0_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_2208,c_2218]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2221,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X2_36,X2_36,X0_36,X0_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_2191,c_2219,c_2220]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2171,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1304,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2222,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) = k1_enumset1(X2_36,X0_36,X1_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_2221,c_2171]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2223,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X2_36,X0_36,X1_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_2181,c_2183,c_2222]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1521,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X0_36,X0_36,X1_36))))) = k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X1_36,X1_36,X1_36))))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_44,c_84]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1600,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X1_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X1_36,X1_36,X1_36))))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1521,c_1593]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1601,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36,X1_36)) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1600,c_1242]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1285,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36,X2_36) = k1_enumset1(X1_36,X2_36,X0_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1267,c_324]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1602,plain,
% 2.60/1.01      ( k5_xboole_0(X0_35,k1_enumset1(X0_36,X0_36,X1_36)) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),X0_35) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1601,c_1285]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3632,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X1_36),X0_35) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),X0_35) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_37,c_1602]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4574,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X2_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k1_enumset1(X0_36,X0_36,X2_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_3632,c_44]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4575,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X0_36),k1_enumset1(X0_36,X2_36,X3_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_3632,c_45]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2175,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X1_36,X0_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1304,c_1267]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2229,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X0_36,X1_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1226,c_2175]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2315,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2229,c_45]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1295,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1283,c_45]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1305,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1295,c_1299]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2199,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X0_36) = k1_enumset1(X0_36,X1_36,X1_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2172,c_1226]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2295,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_2199,c_46]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2344,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X2_36,X3_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X2_36,X3_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_2315,c_1305,c_2295]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4769,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X0_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X3_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_4575,c_2344]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4770,plain,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X2_36,X2_36) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_4574,c_4769]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4771,plain,
% 2.60/1.01      ( k5_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36,X2_36) = k1_enumset1(X2_36,X1_36,X0_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_4770,c_2223]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5579,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X2_36) = k1_enumset1(X0_36,X2_36,X1_36) ),
% 2.60/1.01      inference(light_normalisation,[status(thm)],[c_5578,c_2223,c_4771]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3771,plain,
% 2.60/1.01      ( k1_enumset1(X0_36,X1_36,X2_36) = k1_enumset1(X1_36,X2_36,X0_36) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_1304,c_2222]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_11,negated_conjecture,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.60/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_28,negated_conjecture,
% 2.60/1.01      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_47,negated_conjecture,
% 2.60/1.01      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_28,c_2,c_1]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_61,plain,
% 2.60/1.01      ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k1_enumset1(sK0,sK1,sK2) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_46,c_47]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1213,plain,
% 2.60/1.01      ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_324,c_61]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2157,plain,
% 2.60/1.01      ( k1_enumset1(sK0,sK2,sK1) != k1_enumset1(sK0,sK1,sK2) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_1285,c_1213]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4902,plain,
% 2.60/1.01      ( k1_enumset1(sK1,sK2,sK0) != k1_enumset1(sK0,sK2,sK1) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_3771,c_2157]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5039,plain,
% 2.60/1.01      ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK2,sK0) ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_3771,c_4902]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5589,plain,
% 2.60/1.01      ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK0,sK2) ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_5579,c_5039]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5590,plain,
% 2.60/1.01      ( $false ),
% 2.60/1.01      inference(theory_normalisation,[status(thm)],[c_5589]) ).
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.01  
% 2.60/1.01  ------                               Statistics
% 2.60/1.01  
% 2.60/1.01  ------ General
% 2.60/1.01  
% 2.60/1.01  abstr_ref_over_cycles:                  0
% 2.60/1.01  abstr_ref_under_cycles:                 0
% 2.60/1.01  gc_basic_clause_elim:                   0
% 2.60/1.01  forced_gc_time:                         0
% 2.60/1.01  parsing_time:                           0.013
% 2.60/1.01  unif_index_cands_time:                  0.
% 2.60/1.01  unif_index_add_time:                    0.
% 2.60/1.01  orderings_time:                         0.
% 2.60/1.01  out_proof_time:                         0.013
% 2.60/1.01  total_time:                             0.454
% 2.60/1.01  num_of_symbols:                         40
% 2.60/1.01  num_of_terms:                           17375
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing
% 2.60/1.01  
% 2.60/1.01  num_of_splits:                          0
% 2.60/1.01  num_of_split_atoms:                     0
% 2.60/1.01  num_of_reused_defs:                     0
% 2.60/1.01  num_eq_ax_congr_red:                    24
% 2.60/1.01  num_of_sem_filtered_clauses:            0
% 2.60/1.01  num_of_subtypes:                        2
% 2.60/1.01  monotx_restored_types:                  0
% 2.60/1.01  sat_num_of_epr_types:                   0
% 2.60/1.01  sat_num_of_non_cyclic_types:            0
% 2.60/1.01  sat_guarded_non_collapsed_types:        0
% 2.60/1.01  num_pure_diseq_elim:                    0
% 2.60/1.01  simp_replaced_by:                       0
% 2.60/1.01  res_preprocessed:                       37
% 2.60/1.01  prep_upred:                             0
% 2.60/1.01  prep_unflattend:                        0
% 2.60/1.01  smt_new_axioms:                         0
% 2.60/1.01  pred_elim_cands:                        0
% 2.60/1.01  pred_elim:                              0
% 2.60/1.01  pred_elim_cl:                           0
% 2.60/1.01  pred_elim_cycles:                       0
% 2.60/1.01  merged_defs:                            0
% 2.60/1.01  merged_defs_ncl:                        0
% 2.60/1.01  bin_hyper_res:                          0
% 2.60/1.01  prep_cycles:                            3
% 2.60/1.01  pred_elim_time:                         0.
% 2.60/1.01  splitting_time:                         0.
% 2.60/1.01  sem_filter_time:                        0.
% 2.60/1.01  monotx_time:                            0.
% 2.60/1.01  subtype_inf_time:                       0.
% 2.60/1.01  
% 2.60/1.01  ------ Problem properties
% 2.60/1.01  
% 2.60/1.01  clauses:                                11
% 2.60/1.01  conjectures:                            1
% 2.60/1.01  epr:                                    0
% 2.60/1.01  horn:                                   11
% 2.60/1.01  ground:                                 1
% 2.60/1.01  unary:                                  11
% 2.60/1.01  binary:                                 0
% 2.60/1.01  lits:                                   11
% 2.60/1.01  lits_eq:                                11
% 2.60/1.01  fd_pure:                                0
% 2.60/1.01  fd_pseudo:                              0
% 2.60/1.01  fd_cond:                                0
% 2.60/1.01  fd_pseudo_cond:                         0
% 2.60/1.01  ac_symbols:                             1
% 2.60/1.01  
% 2.60/1.01  ------ Propositional Solver
% 2.60/1.01  
% 2.60/1.01  prop_solver_calls:                      17
% 2.60/1.01  prop_fast_solver_calls:                 86
% 2.60/1.01  smt_solver_calls:                       0
% 2.60/1.01  smt_fast_solver_calls:                  0
% 2.60/1.01  prop_num_of_clauses:                    121
% 2.60/1.01  prop_preprocess_simplified:             519
% 2.60/1.01  prop_fo_subsumed:                       0
% 2.60/1.01  prop_solver_time:                       0.
% 2.60/1.01  smt_solver_time:                        0.
% 2.60/1.01  smt_fast_solver_time:                   0.
% 2.60/1.01  prop_fast_solver_time:                  0.
% 2.60/1.01  prop_unsat_core_time:                   0.
% 2.60/1.01  
% 2.60/1.01  ------ QBF
% 2.60/1.01  
% 2.60/1.01  qbf_q_res:                              0
% 2.60/1.01  qbf_num_tautologies:                    0
% 2.60/1.01  qbf_prep_cycles:                        0
% 2.60/1.01  
% 2.60/1.01  ------ BMC1
% 2.60/1.01  
% 2.60/1.01  bmc1_current_bound:                     -1
% 2.60/1.01  bmc1_last_solved_bound:                 -1
% 2.60/1.01  bmc1_unsat_core_size:                   -1
% 2.60/1.01  bmc1_unsat_core_parents_size:           -1
% 2.60/1.01  bmc1_merge_next_fun:                    0
% 2.60/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.60/1.01  
% 2.60/1.01  ------ Instantiation
% 2.60/1.01  
% 2.60/1.01  inst_num_of_clauses:                    0
% 2.60/1.01  inst_num_in_passive:                    0
% 2.60/1.01  inst_num_in_active:                     0
% 2.60/1.01  inst_num_in_unprocessed:                0
% 2.60/1.01  inst_num_of_loops:                      0
% 2.60/1.01  inst_num_of_learning_restarts:          0
% 2.60/1.01  inst_num_moves_active_passive:          0
% 2.60/1.01  inst_lit_activity:                      0
% 2.60/1.01  inst_lit_activity_moves:                0
% 2.60/1.01  inst_num_tautologies:                   0
% 2.60/1.01  inst_num_prop_implied:                  0
% 2.60/1.01  inst_num_existing_simplified:           0
% 2.60/1.01  inst_num_eq_res_simplified:             0
% 2.60/1.01  inst_num_child_elim:                    0
% 2.60/1.01  inst_num_of_dismatching_blockings:      0
% 2.60/1.01  inst_num_of_non_proper_insts:           0
% 2.60/1.01  inst_num_of_duplicates:                 0
% 2.60/1.01  inst_inst_num_from_inst_to_res:         0
% 2.60/1.01  inst_dismatching_checking_time:         0.
% 2.60/1.01  
% 2.60/1.01  ------ Resolution
% 2.60/1.01  
% 2.60/1.01  res_num_of_clauses:                     0
% 2.60/1.01  res_num_in_passive:                     0
% 2.60/1.01  res_num_in_active:                      0
% 2.60/1.01  res_num_of_loops:                       40
% 2.60/1.01  res_forward_subset_subsumed:            0
% 2.60/1.01  res_backward_subset_subsumed:           0
% 2.60/1.01  res_forward_subsumed:                   0
% 2.60/1.01  res_backward_subsumed:                  0
% 2.60/1.01  res_forward_subsumption_resolution:     0
% 2.60/1.01  res_backward_subsumption_resolution:    0
% 2.60/1.01  res_clause_to_clause_subsumption:       34608
% 2.60/1.01  res_orphan_elimination:                 0
% 2.60/1.01  res_tautology_del:                      1
% 2.60/1.01  res_num_eq_res_simplified:              0
% 2.60/1.01  res_num_sel_changes:                    0
% 2.60/1.01  res_moves_from_active_to_pass:          0
% 2.60/1.01  
% 2.60/1.01  ------ Superposition
% 2.60/1.01  
% 2.60/1.01  sup_time_total:                         0.
% 2.60/1.01  sup_time_generating:                    0.
% 2.60/1.01  sup_time_sim_full:                      0.
% 2.60/1.01  sup_time_sim_immed:                     0.
% 2.60/1.01  
% 2.60/1.01  sup_num_of_clauses:                     1641
% 2.60/1.01  sup_num_in_active:                      60
% 2.60/1.01  sup_num_in_passive:                     1581
% 2.60/1.01  sup_num_of_loops:                       71
% 2.60/1.01  sup_fw_superposition:                   2006
% 2.60/1.01  sup_bw_superposition:                   2640
% 2.60/1.01  sup_immediate_simplified:               976
% 2.60/1.01  sup_given_eliminated:                   2
% 2.60/1.01  comparisons_done:                       0
% 2.60/1.01  comparisons_avoided:                    0
% 2.60/1.01  
% 2.60/1.01  ------ Simplifications
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  sim_fw_subset_subsumed:                 0
% 2.60/1.01  sim_bw_subset_subsumed:                 0
% 2.60/1.01  sim_fw_subsumed:                        20
% 2.60/1.01  sim_bw_subsumed:                        11
% 2.60/1.01  sim_fw_subsumption_res:                 0
% 2.60/1.01  sim_bw_subsumption_res:                 0
% 2.60/1.01  sim_tautology_del:                      0
% 2.60/1.01  sim_eq_tautology_del:                   15
% 2.60/1.01  sim_eq_res_simp:                        0
% 2.60/1.01  sim_fw_demodulated:                     630
% 2.60/1.01  sim_bw_demodulated:                     97
% 2.60/1.01  sim_light_normalised:                   135
% 2.60/1.01  sim_joinable_taut:                      171
% 2.60/1.01  sim_joinable_simp:                      1
% 2.60/1.01  sim_ac_normalised:                      0
% 2.60/1.01  sim_smt_subsumption:                    0
% 2.60/1.01  
%------------------------------------------------------------------------------
