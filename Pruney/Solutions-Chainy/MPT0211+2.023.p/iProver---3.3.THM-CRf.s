%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:27 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 214 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   17 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :   75 ( 223 expanded)
%              Number of equality atoms :   74 ( 222 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f45,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f48,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f32,f41,f39,f48])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f30,f41,f39,f46])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(definition_unfolding,[],[f31,f41,f48,f47])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f40,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f40,f41,f46,f46,f45])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f29,f44,f44])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f26,f44,f44])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( k5_xboole_0(k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35),k5_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k3_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35)))) = k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_6,plain,
    ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( k5_xboole_0(k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35),k5_xboole_0(k6_enumset1(X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35),k3_xboole_0(k6_enumset1(X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35),k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35)))) = k5_xboole_0(k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35),k5_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X8_35),k3_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X8_35),k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_400,plain,
    ( k5_xboole_0(k6_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35),k5_xboole_0(k6_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k3_xboole_0(k6_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k6_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35)))) = k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35) ),
    inference(superposition,[status(thm)],[c_24,c_18])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_21309,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_400,c_17])).

cnf(c_26,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_186,plain,
    ( X0_34 != X1_34
    | X0_34 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X1_34 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1361,plain,
    ( X0_34 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1)
    | X0_34 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_3515,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_5,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,plain,
    ( k6_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k6_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35,X2_35,X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_316,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,plain,
    ( k6_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k6_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X3_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_70,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21309,c_3515,c_316,c_70])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:09:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.85/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/1.48  
% 7.85/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.48  
% 7.85/1.48  ------  iProver source info
% 7.85/1.48  
% 7.85/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.48  git: non_committed_changes: false
% 7.85/1.48  git: last_make_outside_of_git: false
% 7.85/1.48  
% 7.85/1.48  ------ 
% 7.85/1.48  ------ Parsing...
% 7.85/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.48  
% 7.85/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.85/1.48  
% 7.85/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.48  
% 7.85/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.85/1.48  ------ Proving...
% 7.85/1.48  ------ Problem Properties 
% 7.85/1.48  
% 7.85/1.48  
% 7.85/1.48  clauses                                 8
% 7.85/1.48  conjectures                             1
% 7.85/1.48  EPR                                     0
% 7.85/1.48  Horn                                    8
% 7.85/1.48  unary                                   8
% 7.85/1.48  binary                                  0
% 7.85/1.48  lits                                    8
% 7.85/1.48  lits eq                                 8
% 7.85/1.48  fd_pure                                 0
% 7.85/1.48  fd_pseudo                               0
% 7.85/1.48  fd_cond                                 0
% 7.85/1.48  fd_pseudo_cond                          0
% 7.85/1.48  AC symbols                              0
% 7.85/1.48  
% 7.85/1.48  ------ Input Options Time Limit: Unbounded
% 7.85/1.48  
% 7.85/1.48  
% 7.85/1.48  ------ 
% 7.85/1.48  Current options:
% 7.85/1.48  ------ 
% 7.85/1.48  
% 7.85/1.48  
% 7.85/1.48  
% 7.85/1.48  
% 7.85/1.48  ------ Proving...
% 7.85/1.48  
% 7.85/1.48  
% 7.85/1.48  % SZS status Theorem for theBenchmark.p
% 7.85/1.48  
% 7.85/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.48  
% 7.85/1.48  fof(f10,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f32,plain,(
% 7.85/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f10])).
% 7.85/1.48  
% 7.85/1.48  fof(f3,axiom,(
% 7.85/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f25,plain,(
% 7.85/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f3])).
% 7.85/1.48  
% 7.85/1.48  fof(f2,axiom,(
% 7.85/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f24,plain,(
% 7.85/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.85/1.48    inference(cnf_transformation,[],[f2])).
% 7.85/1.48  
% 7.85/1.48  fof(f41,plain,(
% 7.85/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f25,f24])).
% 7.85/1.48  
% 7.85/1.48  fof(f11,axiom,(
% 7.85/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f33,plain,(
% 7.85/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f11])).
% 7.85/1.48  
% 7.85/1.48  fof(f12,axiom,(
% 7.85/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f34,plain,(
% 7.85/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f12])).
% 7.85/1.48  
% 7.85/1.48  fof(f13,axiom,(
% 7.85/1.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f35,plain,(
% 7.85/1.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f13])).
% 7.85/1.48  
% 7.85/1.48  fof(f14,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f36,plain,(
% 7.85/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f14])).
% 7.85/1.48  
% 7.85/1.48  fof(f15,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f37,plain,(
% 7.85/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f15])).
% 7.85/1.48  
% 7.85/1.48  fof(f16,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f38,plain,(
% 7.85/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f16])).
% 7.85/1.48  
% 7.85/1.48  fof(f17,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f39,plain,(
% 7.85/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f17])).
% 7.85/1.48  
% 7.85/1.48  fof(f42,plain,(
% 7.85/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f38,f39])).
% 7.85/1.48  
% 7.85/1.48  fof(f43,plain,(
% 7.85/1.48    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f37,f42])).
% 7.85/1.48  
% 7.85/1.48  fof(f44,plain,(
% 7.85/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f36,f43])).
% 7.85/1.48  
% 7.85/1.48  fof(f45,plain,(
% 7.85/1.48    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f35,f44])).
% 7.85/1.48  
% 7.85/1.48  fof(f46,plain,(
% 7.85/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f34,f45])).
% 7.85/1.48  
% 7.85/1.48  fof(f48,plain,(
% 7.85/1.48    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f33,f46])).
% 7.85/1.48  
% 7.85/1.48  fof(f49,plain,(
% 7.85/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f32,f41,f39,f48])).
% 7.85/1.48  
% 7.85/1.48  fof(f9,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f31,plain,(
% 7.85/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f9])).
% 7.85/1.48  
% 7.85/1.48  fof(f8,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f30,plain,(
% 7.85/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f8])).
% 7.85/1.48  
% 7.85/1.48  fof(f47,plain,(
% 7.85/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f30,f41,f39,f46])).
% 7.85/1.48  
% 7.85/1.48  fof(f54,plain,(
% 7.85/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) )),
% 7.85/1.48    inference(definition_unfolding,[],[f31,f41,f48,f47])).
% 7.85/1.48  
% 7.85/1.48  fof(f18,conjecture,(
% 7.85/1.48    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f19,negated_conjecture,(
% 7.85/1.48    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 7.85/1.48    inference(negated_conjecture,[],[f18])).
% 7.85/1.48  
% 7.85/1.48  fof(f20,plain,(
% 7.85/1.48    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 7.85/1.48    inference(ennf_transformation,[],[f19])).
% 7.85/1.48  
% 7.85/1.48  fof(f21,plain,(
% 7.85/1.48    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 7.85/1.48    introduced(choice_axiom,[])).
% 7.85/1.48  
% 7.85/1.48  fof(f22,plain,(
% 7.85/1.48    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 7.85/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 7.85/1.48  
% 7.85/1.48  fof(f40,plain,(
% 7.85/1.48    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 7.85/1.48    inference(cnf_transformation,[],[f22])).
% 7.85/1.48  
% 7.85/1.48  fof(f55,plain,(
% 7.85/1.48    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 7.85/1.48    inference(definition_unfolding,[],[f40,f41,f46,f46,f45])).
% 7.85/1.48  
% 7.85/1.48  fof(f7,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f29,plain,(
% 7.85/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f7])).
% 7.85/1.48  
% 7.85/1.48  fof(f53,plain,(
% 7.85/1.48    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f29,f44,f44])).
% 7.85/1.48  
% 7.85/1.48  fof(f4,axiom,(
% 7.85/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 7.85/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.48  
% 7.85/1.48  fof(f26,plain,(
% 7.85/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 7.85/1.48    inference(cnf_transformation,[],[f4])).
% 7.85/1.48  
% 7.85/1.48  fof(f50,plain,(
% 7.85/1.48    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1)) )),
% 7.85/1.48    inference(definition_unfolding,[],[f26,f44,f44])).
% 7.85/1.48  
% 7.85/1.48  cnf(c_0,plain,
% 7.85/1.48      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 7.85/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_24,plain,
% 7.85/1.48      ( k5_xboole_0(k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35),k5_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k3_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35)))) = k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35) ),
% 7.85/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_6,plain,
% 7.85/1.48      ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
% 7.85/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_18,plain,
% 7.85/1.48      ( k5_xboole_0(k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35),k5_xboole_0(k6_enumset1(X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35),k3_xboole_0(k6_enumset1(X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35,X8_35),k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35)))) = k5_xboole_0(k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35),k5_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X8_35),k3_xboole_0(k6_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X8_35),k6_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35)))) ),
% 7.85/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_400,plain,
% 7.85/1.48      ( k5_xboole_0(k6_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35),k5_xboole_0(k6_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k3_xboole_0(k6_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k6_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35)))) = k6_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35,X7_35) ),
% 7.85/1.48      inference(superposition,[status(thm)],[c_24,c_18]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_7,negated_conjecture,
% 7.85/1.48      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.85/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_17,negated_conjecture,
% 7.85/1.48      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.85/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_21309,plain,
% 7.85/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.85/1.48      inference(superposition,[status(thm)],[c_400,c_17]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_26,plain,
% 7.85/1.48      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 7.85/1.48      theory(equality) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_186,plain,
% 7.85/1.48      ( X0_34 != X1_34
% 7.85/1.48      | X0_34 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
% 7.85/1.48      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X1_34 ),
% 7.85/1.48      inference(instantiation,[status(thm)],[c_26]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_1361,plain,
% 7.85/1.48      ( X0_34 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1)
% 7.85/1.48      | X0_34 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
% 7.85/1.48      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1) ),
% 7.85/1.48      inference(instantiation,[status(thm)],[c_186]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_3515,plain,
% 7.85/1.48      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1)
% 7.85/1.48      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1)
% 7.85/1.48      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.85/1.48      inference(instantiation,[status(thm)],[c_1361]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_5,plain,
% 7.85/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
% 7.85/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_19,plain,
% 7.85/1.48      ( k6_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k6_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35,X2_35,X1_35,X0_35) ),
% 7.85/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_316,plain,
% 7.85/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1) ),
% 7.85/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_2,plain,
% 7.85/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X1,X2) ),
% 7.85/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_22,plain,
% 7.85/1.48      ( k6_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k6_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X3_35,X1_35,X2_35) ),
% 7.85/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(c_70,plain,
% 7.85/1.48      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK0,sK1) ),
% 7.85/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.85/1.48  
% 7.85/1.48  cnf(contradiction,plain,
% 7.85/1.48      ( $false ),
% 7.85/1.48      inference(minisat,[status(thm)],[c_21309,c_3515,c_316,c_70]) ).
% 7.85/1.48  
% 7.85/1.48  
% 7.85/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.48  
% 7.85/1.48  ------                               Statistics
% 7.85/1.48  
% 7.85/1.48  ------ Selected
% 7.85/1.48  
% 7.85/1.48  total_time:                             0.725
% 7.85/1.48  
%------------------------------------------------------------------------------
