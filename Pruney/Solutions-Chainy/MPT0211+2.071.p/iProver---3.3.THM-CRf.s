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
% DateTime   : Thu Dec  3 11:28:34 EST 2020

% Result     : Theorem 14.76s
% Output     : CNFRefutation 14.76s
% Verified   : 
% Statistics : Number of formulae       :   93 (1172 expanded)
%              Number of clauses        :   43 ( 154 expanded)
%              Number of leaves         :   17 ( 388 expanded)
%              Depth                    :   17
%              Number of atoms          :   94 (1173 expanded)
%              Number of equality atoms :   93 (1172 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f41,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f23,f37,f38,f38])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_enumset1(X0,X1,X2,X3,X4)))) ),
    inference(definition_unfolding,[],[f26,f37,f41,f39])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2))))))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f27,f37,f39,f40])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0)))),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0))))))) ),
    inference(definition_unfolding,[],[f33,f39,f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f25,f38,f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f35,f38,f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f24,f38,f38])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f36,f37,f40,f40,f38])).

cnf(c_3,plain,
    ( k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_enumset1(X0,X1,X2,X3,X4)))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35),k5_xboole_0(k3_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35),k3_xboole_0(k3_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35),k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35)))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_0,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_22,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_473,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35),k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k3_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X2_35,X2_35) ),
    inference(superposition,[status(thm)],[c_19,c_22])).

cnf(c_6272,plain,
    ( k3_enumset1(X0_35,X1_35,X2_35,X2_35,X2_35) = k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_473,c_22])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0)))),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0))))))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35),k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35)))),k5_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35),k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35))))))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35)))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_47,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35)))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35)))) ),
    inference(demodulation,[status(thm)],[c_18,c_22])).

cnf(c_6392,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35),k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35)))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_6272,c_47])).

cnf(c_2,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X2_35,X2_35,X2_35,X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,plain,
    ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X0_35,X0_35,X0_35,X2_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_88,plain,
    ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X1_35,X1_35,X1_35,X2_35,X0_35) ),
    inference(superposition,[status(thm)],[c_20,c_17])).

cnf(c_350,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X3_35,X4_35,X2_35) ),
    inference(superposition,[status(thm)],[c_88,c_22])).

cnf(c_358,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35)))) = k3_enumset1(X1_35,X0_35,X2_35,X3_35,X4_35) ),
    inference(superposition,[status(thm)],[c_88,c_22])).

cnf(c_6570,plain,
    ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X2_35) = k3_enumset1(X1_35,X0_35,X1_35,X2_35,X3_35) ),
    inference(demodulation,[status(thm)],[c_6392,c_350,c_358])).

cnf(c_347,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X4_35,X3_35,X2_35) ),
    inference(superposition,[status(thm)],[c_20,c_22])).

cnf(c_345,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X4_35,X3_35) ),
    inference(superposition,[status(thm)],[c_17,c_22])).

cnf(c_805,plain,
    ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) = k3_enumset1(X0_35,X1_35,X3_35,X4_35,X2_35) ),
    inference(superposition,[status(thm)],[c_347,c_345])).

cnf(c_757,plain,
    ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) = k3_enumset1(X0_35,X1_35,X4_35,X2_35,X3_35) ),
    inference(superposition,[status(thm)],[c_345,c_347])).

cnf(c_1175,plain,
    ( k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35) = k3_enumset1(X1_35,X1_35,X1_35,X2_35,X0_35) ),
    inference(superposition,[status(thm)],[c_757,c_20])).

cnf(c_2533,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35)))) = k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X1_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X0_35,X3_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X0_35,X3_35),k3_enumset1(X1_35,X1_35,X1_35,X1_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_1175,c_19])).

cnf(c_2539,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X1_35)))) = k3_enumset1(X1_35,X0_35,X4_35,X3_35,X2_35) ),
    inference(superposition,[status(thm)],[c_1175,c_347])).

cnf(c_2552,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35)))) = k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X3_35,X4_35),k3_enumset1(X1_35,X1_35,X1_35,X1_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_1175,c_47])).

cnf(c_2569,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35)))) = k3_enumset1(X1_35,X2_35,X4_35,X3_35,X0_35) ),
    inference(demodulation,[status(thm)],[c_2552,c_347])).

cnf(c_2583,plain,
    ( k3_enumset1(X0_35,X1_35,X2_35,X2_35,X3_35) = k3_enumset1(X0_35,X0_35,X2_35,X3_35,X1_35) ),
    inference(demodulation,[status(thm)],[c_2533,c_2539,c_2569])).

cnf(c_10136,plain,
    ( k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35) = k3_enumset1(X0_35,X3_35,X2_35,X1_35,X1_35) ),
    inference(superposition,[status(thm)],[c_805,c_2583])).

cnf(c_560,plain,
    ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) = k3_enumset1(X0_35,X1_35,X2_35,X4_35,X3_35) ),
    inference(superposition,[status(thm)],[c_345,c_22])).

cnf(c_1,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,plain,
    ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X2_35,X2_35,X2_35,X0_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_42,plain,
    ( k3_enumset1(sK1,sK0,sK2,sK2,sK0) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_16,c_22])).

cnf(c_95,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK2,sK0) != k3_enumset1(sK1,sK0,sK2,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_21,c_42])).

cnf(c_691,plain,
    ( k3_enumset1(sK1,sK0,sK2,sK0,sK2) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_560,c_95])).

cnf(c_1130,plain,
    ( k3_enumset1(sK1,sK0,sK0,sK2,sK2) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_757,c_691])).

cnf(c_47610,plain,
    ( k3_enumset1(sK1,sK1,sK2,sK0,sK0) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_10136,c_1130])).

cnf(c_49039,plain,
    ( k3_enumset1(sK1,sK1,sK0,sK2,sK0) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(superposition,[status(thm)],[c_805,c_47610])).

cnf(c_52828,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK0,sK2) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(superposition,[status(thm)],[c_6570,c_49039])).

cnf(c_863,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK0,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52828,c_863])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 14.76/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.76/2.51  
% 14.76/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.76/2.51  
% 14.76/2.51  ------  iProver source info
% 14.76/2.51  
% 14.76/2.51  git: date: 2020-06-30 10:37:57 +0100
% 14.76/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.76/2.51  git: non_committed_changes: false
% 14.76/2.51  git: last_make_outside_of_git: false
% 14.76/2.51  
% 14.76/2.51  ------ 
% 14.76/2.51  ------ Parsing...
% 14.76/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.76/2.51  
% 14.76/2.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.76/2.51  
% 14.76/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.76/2.51  
% 14.76/2.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.76/2.51  ------ Proving...
% 14.76/2.51  ------ Problem Properties 
% 14.76/2.51  
% 14.76/2.51  
% 14.76/2.51  clauses                                 7
% 14.76/2.51  conjectures                             1
% 14.76/2.51  EPR                                     0
% 14.76/2.51  Horn                                    7
% 14.76/2.51  unary                                   7
% 14.76/2.51  binary                                  0
% 14.76/2.51  lits                                    7
% 14.76/2.51  lits eq                                 7
% 14.76/2.51  fd_pure                                 0
% 14.76/2.51  fd_pseudo                               0
% 14.76/2.51  fd_cond                                 0
% 14.76/2.51  fd_pseudo_cond                          0
% 14.76/2.51  AC symbols                              0
% 14.76/2.51  
% 14.76/2.51  ------ Input Options Time Limit: Unbounded
% 14.76/2.51  
% 14.76/2.51  
% 14.76/2.51  ------ 
% 14.76/2.51  Current options:
% 14.76/2.51  ------ 
% 14.76/2.51  
% 14.76/2.51  
% 14.76/2.51  
% 14.76/2.51  
% 14.76/2.51  ------ Proving...
% 14.76/2.51  
% 14.76/2.51  
% 14.76/2.51  % SZS status Theorem for theBenchmark.p
% 14.76/2.51  
% 14.76/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 14.76/2.51  
% 14.76/2.51  fof(f6,axiom,(
% 14.76/2.51    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f26,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f6])).
% 14.76/2.51  
% 14.76/2.51  fof(f8,axiom,(
% 14.76/2.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f28,plain,(
% 14.76/2.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f8])).
% 14.76/2.51  
% 14.76/2.51  fof(f9,axiom,(
% 14.76/2.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f29,plain,(
% 14.76/2.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f9])).
% 14.76/2.51  
% 14.76/2.51  fof(f40,plain,(
% 14.76/2.51    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f29,f38])).
% 14.76/2.51  
% 14.76/2.51  fof(f41,plain,(
% 14.76/2.51    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f28,f40])).
% 14.76/2.51  
% 14.76/2.51  fof(f3,axiom,(
% 14.76/2.51    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f23,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f3])).
% 14.76/2.51  
% 14.76/2.51  fof(f2,axiom,(
% 14.76/2.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f22,plain,(
% 14.76/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f2])).
% 14.76/2.51  
% 14.76/2.51  fof(f1,axiom,(
% 14.76/2.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f21,plain,(
% 14.76/2.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.76/2.51    inference(cnf_transformation,[],[f1])).
% 14.76/2.51  
% 14.76/2.51  fof(f37,plain,(
% 14.76/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f22,f21])).
% 14.76/2.51  
% 14.76/2.51  fof(f10,axiom,(
% 14.76/2.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f30,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f10])).
% 14.76/2.51  
% 14.76/2.51  fof(f11,axiom,(
% 14.76/2.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f31,plain,(
% 14.76/2.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f11])).
% 14.76/2.51  
% 14.76/2.51  fof(f38,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f30,f31])).
% 14.76/2.51  
% 14.76/2.51  fof(f39,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f23,f37,f38,f38])).
% 14.76/2.51  
% 14.76/2.51  fof(f47,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_enumset1(X0,X1,X2,X3,X4))))) )),
% 14.76/2.51    inference(definition_unfolding,[],[f26,f37,f41,f39])).
% 14.76/2.51  
% 14.76/2.51  fof(f12,axiom,(
% 14.76/2.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f32,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f12])).
% 14.76/2.51  
% 14.76/2.51  fof(f44,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f32,f39])).
% 14.76/2.51  
% 14.76/2.51  fof(f13,axiom,(
% 14.76/2.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f33,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f13])).
% 14.76/2.51  
% 14.76/2.51  fof(f14,axiom,(
% 14.76/2.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f34,plain,(
% 14.76/2.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f14])).
% 14.76/2.51  
% 14.76/2.51  fof(f7,axiom,(
% 14.76/2.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f27,plain,(
% 14.76/2.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f7])).
% 14.76/2.51  
% 14.76/2.51  fof(f42,plain,(
% 14.76/2.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2))))))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f27,f37,f39,f40])).
% 14.76/2.51  
% 14.76/2.51  fof(f43,plain,(
% 14.76/2.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f34,f42])).
% 14.76/2.51  
% 14.76/2.51  fof(f48,plain,(
% 14.76/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0)))),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0)))))))) )),
% 14.76/2.51    inference(definition_unfolding,[],[f33,f39,f43])).
% 14.76/2.51  
% 14.76/2.51  fof(f5,axiom,(
% 14.76/2.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f25,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f5])).
% 14.76/2.51  
% 14.76/2.51  fof(f46,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f25,f38,f38])).
% 14.76/2.51  
% 14.76/2.51  fof(f15,axiom,(
% 14.76/2.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f35,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f15])).
% 14.76/2.51  
% 14.76/2.51  fof(f49,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X0,X0,X2,X1)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f35,f38,f38])).
% 14.76/2.51  
% 14.76/2.51  fof(f4,axiom,(
% 14.76/2.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f24,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 14.76/2.51    inference(cnf_transformation,[],[f4])).
% 14.76/2.51  
% 14.76/2.51  fof(f45,plain,(
% 14.76/2.51    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0)) )),
% 14.76/2.51    inference(definition_unfolding,[],[f24,f38,f38])).
% 14.76/2.51  
% 14.76/2.51  fof(f16,conjecture,(
% 14.76/2.51    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 14.76/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.76/2.51  
% 14.76/2.51  fof(f17,negated_conjecture,(
% 14.76/2.51    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 14.76/2.51    inference(negated_conjecture,[],[f16])).
% 14.76/2.51  
% 14.76/2.51  fof(f18,plain,(
% 14.76/2.51    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 14.76/2.51    inference(ennf_transformation,[],[f17])).
% 14.76/2.51  
% 14.76/2.51  fof(f19,plain,(
% 14.76/2.51    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 14.76/2.51    introduced(choice_axiom,[])).
% 14.76/2.51  
% 14.76/2.51  fof(f20,plain,(
% 14.76/2.51    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 14.76/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 14.76/2.51  
% 14.76/2.51  fof(f36,plain,(
% 14.76/2.51    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 14.76/2.51    inference(cnf_transformation,[],[f20])).
% 14.76/2.51  
% 14.76/2.51  fof(f50,plain,(
% 14.76/2.51    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 14.76/2.51    inference(definition_unfolding,[],[f36,f37,f40,f40,f38])).
% 14.76/2.51  
% 14.76/2.51  cnf(c_3,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_enumset1(X0,X1,X2,X3,X4)))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) ),
% 14.76/2.51      inference(cnf_transformation,[],[f47]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_19,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35),k5_xboole_0(k3_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35),k3_xboole_0(k3_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35),k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35)))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35)))) ),
% 14.76/2.51      inference(subtyping,[status(esa)],[c_3]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_0,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 14.76/2.51      inference(cnf_transformation,[],[f44]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_22,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) ),
% 14.76/2.51      inference(subtyping,[status(esa)],[c_0]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_473,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35),k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k3_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X2_35,X2_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_19,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_6272,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X1_35,X2_35,X2_35,X2_35) = k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_473,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_4,plain,
% 14.76/2.51      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0)))),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X0,X0,X0,X0,X0))))))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) ),
% 14.76/2.51      inference(cnf_transformation,[],[f48]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_18,plain,
% 14.76/2.51      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35),k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35)))),k5_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35),k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35))))))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35)))) ),
% 14.76/2.51      inference(subtyping,[status(esa)],[c_4]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_47,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35)))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X4_35,X5_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35)))) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_18,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_6392,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35),k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35)))) = k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X3_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X3_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_6272,c_47]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_2,plain,
% 14.76/2.51      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
% 14.76/2.51      inference(cnf_transformation,[],[f46]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_20,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X2_35,X2_35,X2_35,X1_35,X0_35) ),
% 14.76/2.51      inference(subtyping,[status(esa)],[c_2]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_5,plain,
% 14.76/2.51      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X0,X0,X2,X1) ),
% 14.76/2.51      inference(cnf_transformation,[],[f49]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_17,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X0_35,X0_35,X0_35,X2_35,X1_35) ),
% 14.76/2.51      inference(subtyping,[status(esa)],[c_5]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_88,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X1_35,X1_35,X1_35,X2_35,X0_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_20,c_17]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_350,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X3_35,X4_35,X2_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_88,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_358,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X1_35,X1_35)))) = k3_enumset1(X1_35,X0_35,X2_35,X3_35,X4_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_88,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_6570,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X2_35) = k3_enumset1(X1_35,X0_35,X1_35,X2_35,X3_35) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_6392,c_350,c_358]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_347,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X4_35,X3_35,X2_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_20,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_345,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X4_35,X3_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_17,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_805,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) = k3_enumset1(X0_35,X1_35,X3_35,X4_35,X2_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_347,c_345]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_757,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) = k3_enumset1(X0_35,X1_35,X4_35,X2_35,X3_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_345,c_347]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_1175,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35) = k3_enumset1(X1_35,X1_35,X1_35,X2_35,X0_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_757,c_20]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_2533,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35)))) = k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X1_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X0_35,X3_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X0_35,X3_35),k3_enumset1(X1_35,X1_35,X1_35,X1_35,X1_35)))) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_1175,c_19]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_2539,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X1_35)))) = k3_enumset1(X1_35,X0_35,X4_35,X3_35,X2_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_1175,c_347]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_2552,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35)))) = k5_xboole_0(k3_enumset1(X1_35,X1_35,X1_35,X1_35,X2_35),k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X3_35,X4_35),k3_enumset1(X1_35,X1_35,X1_35,X1_35,X2_35)))) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_1175,c_47]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_2569,plain,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35),k5_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_xboole_0(k3_enumset1(X3_35,X3_35,X3_35,X3_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X0_35,X2_35)))) = k3_enumset1(X1_35,X2_35,X4_35,X3_35,X0_35) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_2552,c_347]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_2583,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X1_35,X2_35,X2_35,X3_35) = k3_enumset1(X0_35,X0_35,X2_35,X3_35,X1_35) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_2533,c_2539,c_2569]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_10136,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35) = k3_enumset1(X0_35,X3_35,X2_35,X1_35,X1_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_805,c_2583]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_560,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) = k3_enumset1(X0_35,X1_35,X2_35,X4_35,X3_35) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_345,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_1,plain,
% 14.76/2.51      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X0,X1) ),
% 14.76/2.51      inference(cnf_transformation,[],[f45]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_21,plain,
% 14.76/2.51      ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X2_35,X2_35,X2_35,X0_35,X1_35) ),
% 14.76/2.51      inference(subtyping,[status(esa)],[c_1]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_6,negated_conjecture,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 14.76/2.51      inference(cnf_transformation,[],[f50]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_16,negated_conjecture,
% 14.76/2.51      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)))) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 14.76/2.51      inference(subtyping,[status(esa)],[c_6]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_42,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK0,sK2,sK2,sK0) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_16,c_22]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_95,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK1,sK1,sK2,sK0) != k3_enumset1(sK1,sK0,sK2,sK2,sK0) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_21,c_42]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_691,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK0,sK2,sK0,sK2) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_560,c_95]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_1130,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK0,sK0,sK2,sK2) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_757,c_691]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_47610,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK1,sK2,sK0,sK0) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
% 14.76/2.51      inference(demodulation,[status(thm)],[c_10136,c_1130]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_49039,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK1,sK0,sK2,sK0) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_805,c_47610]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_52828,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK1,sK1,sK0,sK2) != k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
% 14.76/2.51      inference(superposition,[status(thm)],[c_6570,c_49039]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(c_863,plain,
% 14.76/2.51      ( k3_enumset1(sK1,sK1,sK1,sK0,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
% 14.76/2.51      inference(instantiation,[status(thm)],[c_17]) ).
% 14.76/2.51  
% 14.76/2.51  cnf(contradiction,plain,
% 14.76/2.51      ( $false ),
% 14.76/2.51      inference(minisat,[status(thm)],[c_52828,c_863]) ).
% 14.76/2.51  
% 14.76/2.51  
% 14.76/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 14.76/2.51  
% 14.76/2.51  ------                               Statistics
% 14.76/2.51  
% 14.76/2.51  ------ Selected
% 14.76/2.51  
% 14.76/2.51  total_time:                             1.801
% 14.76/2.51  
%------------------------------------------------------------------------------
