%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:47 EST 2020

% Result     : Theorem 15.84s
% Output     : CNFRefutation 15.84s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 631 expanded)
%              Number of clauses        :   28 (  71 expanded)
%              Number of leaves         :   16 ( 210 expanded)
%              Depth                    :   17
%              Number of atoms          :   73 ( 632 expanded)
%              Number of equality atoms :   72 ( 631 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2) ),
    inference(definition_unfolding,[],[f31,f36,f36])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f38,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f22,f33,f29,f38])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f23,f33,f29,f37])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f21,f33,f34,f34])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k3_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f24,f33,f37,f35])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f32,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

cnf(c_3,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k4_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_0,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36),k5_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36),k3_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36),k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36)))) = k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1300,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_14,c_17])).

cnf(c_1795,plain,
    ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X4_36),k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36))))))) = k4_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_1300,c_17])).

cnf(c_2,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36)))) = k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1294,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X4_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k4_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_1807,plain,
    ( k4_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X4_36) = k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_1795,c_17,c_1294])).

cnf(c_1304,plain,
    ( k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X4_36) = k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_17,c_15])).

cnf(c_1859,plain,
    ( k4_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36,X3_36) = k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1807,c_1304])).

cnf(c_1872,plain,
    ( k4_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36) = k4_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1807,c_14])).

cnf(c_3495,plain,
    ( k4_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36) = k4_enumset1(X1_36,X1_36,X0_36,X0_36,X2_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1859,c_1872])).

cnf(c_1,plain,
    ( k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k3_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5)))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k4_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X7_36),k3_xboole_0(k4_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X7_36),k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36,X7_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36,X7_36),k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36)))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1514,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X4_36),k5_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k3_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X4_36)))) = k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X4_36,X6_36),k3_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X4_36,X6_36),k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_14,c_16])).

cnf(c_49091,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36),k5_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36),k3_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36)))) = k5_xboole_0(k4_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X3_36),k5_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X4_36),k4_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_3495,c_1514])).

cnf(c_1637,plain,
    ( k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X3_36) = k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1294,c_17])).

cnf(c_1683,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_xboole_0(k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_1637,c_16])).

cnf(c_1744,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k4_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36,X5_36) ),
    inference(demodulation,[status(thm)],[c_1683,c_15])).

cnf(c_50096,plain,
    ( k4_enumset1(X0_36,X1_36,X1_36,X2_36,X3_36,X4_36) = k4_enumset1(X0_36,X1_36,X0_36,X3_36,X2_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_49091,c_15,c_1744])).

cnf(c_4,negated_conjecture,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_50335,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_50096,c_13])).

cnf(c_18,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_4559,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50335,c_4559])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.84/2.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.84/2.54  
% 15.84/2.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.84/2.54  
% 15.84/2.54  ------  iProver source info
% 15.84/2.54  
% 15.84/2.54  git: date: 2020-06-30 10:37:57 +0100
% 15.84/2.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.84/2.54  git: non_committed_changes: false
% 15.84/2.54  git: last_make_outside_of_git: false
% 15.84/2.54  
% 15.84/2.54  ------ 
% 15.84/2.54  ------ Parsing...
% 15.84/2.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  ------ Proving...
% 15.84/2.54  ------ Problem Properties 
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  clauses                                 5
% 15.84/2.54  conjectures                             1
% 15.84/2.54  EPR                                     0
% 15.84/2.54  Horn                                    5
% 15.84/2.54  unary                                   5
% 15.84/2.54  binary                                  0
% 15.84/2.54  lits                                    5
% 15.84/2.54  lits eq                                 5
% 15.84/2.54  fd_pure                                 0
% 15.84/2.54  fd_pseudo                               0
% 15.84/2.54  fd_cond                                 0
% 15.84/2.54  fd_pseudo_cond                          0
% 15.84/2.54  AC symbols                              0
% 15.84/2.54  
% 15.84/2.54  ------ Input Options Time Limit: Unbounded
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing...
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 15.84/2.54  Current options:
% 15.84/2.54  ------ 
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing...
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing...
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing...
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.84/2.54  
% 15.84/2.54  ------ Proving...
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  % SZS status Theorem for theBenchmark.p
% 15.84/2.54  
% 15.84/2.54  % SZS output start CNFRefutation for theBenchmark.p
% 15.84/2.54  
% 15.84/2.54  fof(f13,axiom,(
% 15.84/2.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f31,plain,(
% 15.84/2.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f13])).
% 15.84/2.54  
% 15.84/2.54  fof(f9,axiom,(
% 15.84/2.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f27,plain,(
% 15.84/2.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f9])).
% 15.84/2.54  
% 15.84/2.54  fof(f10,axiom,(
% 15.84/2.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f28,plain,(
% 15.84/2.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f10])).
% 15.84/2.54  
% 15.84/2.54  fof(f11,axiom,(
% 15.84/2.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f29,plain,(
% 15.84/2.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f11])).
% 15.84/2.54  
% 15.84/2.54  fof(f34,plain,(
% 15.84/2.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f28,f29])).
% 15.84/2.54  
% 15.84/2.54  fof(f36,plain,(
% 15.84/2.54    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f27,f34])).
% 15.84/2.54  
% 15.84/2.54  fof(f43,plain,(
% 15.84/2.54    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f31,f36,f36])).
% 15.84/2.54  
% 15.84/2.54  fof(f4,axiom,(
% 15.84/2.54    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f22,plain,(
% 15.84/2.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f4])).
% 15.84/2.54  
% 15.84/2.54  fof(f2,axiom,(
% 15.84/2.54    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f20,plain,(
% 15.84/2.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f2])).
% 15.84/2.54  
% 15.84/2.54  fof(f1,axiom,(
% 15.84/2.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f19,plain,(
% 15.84/2.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.84/2.54    inference(cnf_transformation,[],[f1])).
% 15.84/2.54  
% 15.84/2.54  fof(f33,plain,(
% 15.84/2.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f20,f19])).
% 15.84/2.54  
% 15.84/2.54  fof(f7,axiom,(
% 15.84/2.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f25,plain,(
% 15.84/2.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f7])).
% 15.84/2.54  
% 15.84/2.54  fof(f8,axiom,(
% 15.84/2.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f26,plain,(
% 15.84/2.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f8])).
% 15.84/2.54  
% 15.84/2.54  fof(f37,plain,(
% 15.84/2.54    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f26,f36])).
% 15.84/2.54  
% 15.84/2.54  fof(f38,plain,(
% 15.84/2.54    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f25,f37])).
% 15.84/2.54  
% 15.84/2.54  fof(f40,plain,(
% 15.84/2.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f22,f33,f29,f38])).
% 15.84/2.54  
% 15.84/2.54  fof(f12,axiom,(
% 15.84/2.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f30,plain,(
% 15.84/2.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f12])).
% 15.84/2.54  
% 15.84/2.54  fof(f5,axiom,(
% 15.84/2.54    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f23,plain,(
% 15.84/2.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f5])).
% 15.84/2.54  
% 15.84/2.54  fof(f39,plain,(
% 15.84/2.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f23,f33,f29,f37])).
% 15.84/2.54  
% 15.84/2.54  fof(f42,plain,(
% 15.84/2.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f30,f39])).
% 15.84/2.54  
% 15.84/2.54  fof(f6,axiom,(
% 15.84/2.54    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f24,plain,(
% 15.84/2.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f6])).
% 15.84/2.54  
% 15.84/2.54  fof(f3,axiom,(
% 15.84/2.54    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f21,plain,(
% 15.84/2.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 15.84/2.54    inference(cnf_transformation,[],[f3])).
% 15.84/2.54  
% 15.84/2.54  fof(f35,plain,(
% 15.84/2.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 15.84/2.54    inference(definition_unfolding,[],[f21,f33,f34,f34])).
% 15.84/2.54  
% 15.84/2.54  fof(f41,plain,(
% 15.84/2.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k3_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5))))) )),
% 15.84/2.54    inference(definition_unfolding,[],[f24,f33,f37,f35])).
% 15.84/2.54  
% 15.84/2.54  fof(f14,conjecture,(
% 15.84/2.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 15.84/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.54  
% 15.84/2.54  fof(f15,negated_conjecture,(
% 15.84/2.54    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 15.84/2.54    inference(negated_conjecture,[],[f14])).
% 15.84/2.54  
% 15.84/2.54  fof(f16,plain,(
% 15.84/2.54    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 15.84/2.54    inference(ennf_transformation,[],[f15])).
% 15.84/2.54  
% 15.84/2.54  fof(f17,plain,(
% 15.84/2.54    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 15.84/2.54    introduced(choice_axiom,[])).
% 15.84/2.54  
% 15.84/2.54  fof(f18,plain,(
% 15.84/2.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 15.84/2.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 15.84/2.54  
% 15.84/2.54  fof(f32,plain,(
% 15.84/2.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 15.84/2.54    inference(cnf_transformation,[],[f18])).
% 15.84/2.54  
% 15.84/2.54  fof(f44,plain,(
% 15.84/2.54    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3)),
% 15.84/2.54    inference(definition_unfolding,[],[f32,f34,f34])).
% 15.84/2.54  
% 15.84/2.54  cnf(c_3,plain,
% 15.84/2.54      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2) ),
% 15.84/2.54      inference(cnf_transformation,[],[f43]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_14,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k4_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 15.84/2.54      inference(subtyping,[status(esa)],[c_3]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_0,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 15.84/2.54      inference(cnf_transformation,[],[f40]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_17,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36),k5_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36),k3_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36),k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36)))) = k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36) ),
% 15.84/2.54      inference(subtyping,[status(esa)],[c_0]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1300,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_14,c_17]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1795,plain,
% 15.84/2.54      ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X4_36),k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36))))))) = k4_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_1300,c_17]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_2,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 15.84/2.54      inference(cnf_transformation,[],[f42]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_15,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36)))) = k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36) ),
% 15.84/2.54      inference(subtyping,[status(esa)],[c_2]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1294,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X4_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k4_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1807,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X4_36) = k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 15.84/2.54      inference(demodulation,[status(thm)],[c_1795,c_17,c_1294]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1304,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X4_36) = k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_17,c_15]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1859,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36,X3_36) = k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_1807,c_1304]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1872,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36) = k4_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_1807,c_14]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_3495,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X0_36,X0_36,X1_36,X1_36,X2_36) = k4_enumset1(X1_36,X1_36,X0_36,X0_36,X2_36,X2_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_1859,c_1872]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k3_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5)))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
% 15.84/2.54      inference(cnf_transformation,[],[f41]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_16,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k4_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X7_36),k3_xboole_0(k4_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X7_36),k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36,X7_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X5_36,X6_36,X7_36),k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36)))) ),
% 15.84/2.54      inference(subtyping,[status(esa)],[c_1]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1514,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X4_36),k5_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k3_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X4_36)))) = k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X4_36,X6_36),k3_xboole_0(k4_enumset1(X5_36,X5_36,X5_36,X5_36,X4_36,X6_36),k4_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36)))) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_14,c_16]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_49091,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36),k5_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36),k3_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X1_36)))) = k5_xboole_0(k4_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X3_36),k5_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k4_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X4_36),k4_enumset1(X1_36,X1_36,X1_36,X0_36,X0_36,X3_36)))) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_3495,c_1514]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1637,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X3_36) = k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_1294,c_17]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1683,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_xboole_0(k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36),k4_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36,X3_36)))) ),
% 15.84/2.54      inference(superposition,[status(thm)],[c_1637,c_16]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_1744,plain,
% 15.84/2.54      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k3_xboole_0(k4_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36),k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k4_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36,X5_36) ),
% 15.84/2.54      inference(demodulation,[status(thm)],[c_1683,c_15]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_50096,plain,
% 15.84/2.54      ( k4_enumset1(X0_36,X1_36,X1_36,X2_36,X3_36,X4_36) = k4_enumset1(X0_36,X1_36,X0_36,X3_36,X2_36,X4_36) ),
% 15.84/2.54      inference(demodulation,[status(thm)],[c_49091,c_15,c_1744]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_4,negated_conjecture,
% 15.84/2.54      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) ),
% 15.84/2.54      inference(cnf_transformation,[],[f44]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_13,negated_conjecture,
% 15.84/2.54      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) ),
% 15.84/2.54      inference(subtyping,[status(esa)],[c_4]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_50335,plain,
% 15.84/2.54      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 15.84/2.54      inference(demodulation,[status(thm)],[c_50096,c_13]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_18,plain,( X0_35 = X0_35 ),theory(equality) ).
% 15.84/2.54  
% 15.84/2.54  cnf(c_4559,plain,
% 15.84/2.54      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 15.84/2.54      inference(instantiation,[status(thm)],[c_18]) ).
% 15.84/2.54  
% 15.84/2.54  cnf(contradiction,plain,
% 15.84/2.54      ( $false ),
% 15.84/2.54      inference(minisat,[status(thm)],[c_50335,c_4559]) ).
% 15.84/2.54  
% 15.84/2.54  
% 15.84/2.54  % SZS output end CNFRefutation for theBenchmark.p
% 15.84/2.54  
% 15.84/2.54  ------                               Statistics
% 15.84/2.54  
% 15.84/2.54  ------ Selected
% 15.84/2.54  
% 15.84/2.54  total_time:                             1.865
% 15.84/2.54  
%------------------------------------------------------------------------------
