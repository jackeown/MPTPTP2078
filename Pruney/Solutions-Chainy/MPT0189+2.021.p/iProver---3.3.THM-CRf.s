%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:54 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 218 expanded)
%              Number of clauses        :   20 (  24 expanded)
%              Number of leaves         :   16 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 219 expanded)
%              Number of equality atoms :   67 ( 218 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f46,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f47,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f29,f41,f38,f47])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f25,f41,f43,f43])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f27,f43,f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f26,f45,f45])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f40,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f40,f43,f43])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f28,f43,f43])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k3_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_318,plain,
    ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_25,c_18])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X3_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2404,plain,
    ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X3_36,X2_36) ),
    inference(superposition,[status(thm)],[c_318,c_23])).

cnf(c_1,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_209,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X2_36,X0_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(superposition,[status(thm)],[c_24,c_18])).

cnf(c_10246,plain,
    ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
    inference(superposition,[status(thm)],[c_25,c_209])).

cnf(c_8,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_12397,plain,
    ( k5_enumset1(sK0,sK2,sK1,sK3,sK3,sK3,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_10246,c_17])).

cnf(c_14694,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK3,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2404,c_12397])).

cnf(c_3,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_183,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK3,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14694,c_183])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:28:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.00  
% 3.62/1.00  ------  iProver source info
% 3.62/1.00  
% 3.62/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.00  git: non_committed_changes: false
% 3.62/1.00  git: last_make_outside_of_git: false
% 3.62/1.00  
% 3.62/1.00  ------ 
% 3.62/1.00  ------ Parsing...
% 3.62/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.00  
% 3.62/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.62/1.00  
% 3.62/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.00  
% 3.62/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/1.00  ------ Proving...
% 3.62/1.00  ------ Problem Properties 
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  clauses                                 9
% 3.62/1.00  conjectures                             1
% 3.62/1.00  EPR                                     0
% 3.62/1.00  Horn                                    9
% 3.62/1.00  unary                                   9
% 3.62/1.00  binary                                  0
% 3.62/1.00  lits                                    9
% 3.62/1.00  lits eq                                 9
% 3.62/1.00  fd_pure                                 0
% 3.62/1.00  fd_pseudo                               0
% 3.62/1.00  fd_cond                                 0
% 3.62/1.00  fd_pseudo_cond                          0
% 3.62/1.00  AC symbols                              0
% 3.62/1.00  
% 3.62/1.00  ------ Input Options Time Limit: Unbounded
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  ------ 
% 3.62/1.00  Current options:
% 3.62/1.00  ------ 
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  ------ Proving...
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  % SZS status Theorem for theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  fof(f7,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f29,plain,(
% 3.62/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f7])).
% 3.62/1.00  
% 3.62/1.00  fof(f2,axiom,(
% 3.62/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f24,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f2])).
% 3.62/1.00  
% 3.62/1.00  fof(f1,axiom,(
% 3.62/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f23,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.62/1.00    inference(cnf_transformation,[],[f1])).
% 3.62/1.00  
% 3.62/1.00  fof(f41,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f24,f23])).
% 3.62/1.00  
% 3.62/1.00  fof(f11,axiom,(
% 3.62/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f33,plain,(
% 3.62/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f11])).
% 3.62/1.00  
% 3.62/1.00  fof(f12,axiom,(
% 3.62/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f34,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f12])).
% 3.62/1.00  
% 3.62/1.00  fof(f13,axiom,(
% 3.62/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f35,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f13])).
% 3.62/1.00  
% 3.62/1.00  fof(f14,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f36,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f14])).
% 3.62/1.00  
% 3.62/1.00  fof(f15,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f37,plain,(
% 3.62/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f15])).
% 3.62/1.00  
% 3.62/1.00  fof(f16,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f38,plain,(
% 3.62/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f16])).
% 3.62/1.00  
% 3.62/1.00  fof(f42,plain,(
% 3.62/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f37,f38])).
% 3.62/1.00  
% 3.62/1.00  fof(f43,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f36,f42])).
% 3.62/1.00  
% 3.62/1.00  fof(f45,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f35,f43])).
% 3.62/1.00  
% 3.62/1.00  fof(f46,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f34,f45])).
% 3.62/1.00  
% 3.62/1.00  fof(f47,plain,(
% 3.62/1.00    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f33,f46])).
% 3.62/1.00  
% 3.62/1.00  fof(f48,plain,(
% 3.62/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f29,f41,f38,f47])).
% 3.62/1.00  
% 3.62/1.00  fof(f17,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f39,plain,(
% 3.62/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f17])).
% 3.62/1.00  
% 3.62/1.00  fof(f3,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f25,plain,(
% 3.62/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f3])).
% 3.62/1.00  
% 3.62/1.00  fof(f44,plain,(
% 3.62/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f25,f41,f43,f43])).
% 3.62/1.00  
% 3.62/1.00  fof(f55,plain,(
% 3.62/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f39,f44])).
% 3.62/1.00  
% 3.62/1.00  fof(f5,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f27,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f5])).
% 3.62/1.00  
% 3.62/1.00  fof(f50,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f27,f43,f43])).
% 3.62/1.00  
% 3.62/1.00  fof(f4,axiom,(
% 3.62/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f26,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f4])).
% 3.62/1.00  
% 3.62/1.00  fof(f49,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f26,f45,f45])).
% 3.62/1.00  
% 3.62/1.00  fof(f18,conjecture,(
% 3.62/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f19,negated_conjecture,(
% 3.62/1.00    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.62/1.00    inference(negated_conjecture,[],[f18])).
% 3.62/1.00  
% 3.62/1.00  fof(f20,plain,(
% 3.62/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 3.62/1.00    inference(ennf_transformation,[],[f19])).
% 3.62/1.00  
% 3.62/1.00  fof(f21,plain,(
% 3.62/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.62/1.00    introduced(choice_axiom,[])).
% 3.62/1.00  
% 3.62/1.00  fof(f22,plain,(
% 3.62/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.62/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 3.62/1.00  
% 3.62/1.00  fof(f40,plain,(
% 3.62/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.62/1.00    inference(cnf_transformation,[],[f22])).
% 3.62/1.00  
% 3.62/1.00  fof(f56,plain,(
% 3.62/1.00    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3)),
% 3.62/1.00    inference(definition_unfolding,[],[f40,f43,f43])).
% 3.62/1.00  
% 3.62/1.00  fof(f6,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 3.62/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f28,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f6])).
% 3.62/1.00  
% 3.62/1.00  fof(f51,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f28,f43,f43])).
% 3.62/1.00  
% 3.62/1.00  cnf(c_0,plain,
% 3.62/1.00      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.62/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_25,plain,
% 3.62/1.00      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k3_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 3.62/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_7,plain,
% 3.62/1.00      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.62/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_18,plain,
% 3.62/1.00      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 3.62/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_318,plain,
% 3.62/1.00      ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_25,c_18]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2,plain,
% 3.62/1.00      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2) ),
% 3.62/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_23,plain,
% 3.62/1.00      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X3_36,X2_36) ),
% 3.62/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2404,plain,
% 3.62/1.00      ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X3_36,X2_36) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_318,c_23]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1,plain,
% 3.62/1.00      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 3.62/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_24,plain,
% 3.62/1.00      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
% 3.62/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_209,plain,
% 3.62/1.00      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X2_36,X0_36,X3_36,X4_36,X5_36,X6_36) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_24,c_18]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10246,plain,
% 3.62/1.00      ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_25,c_209]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_8,negated_conjecture,
% 3.62/1.00      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 3.62/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_17,negated_conjecture,
% 3.62/1.00      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 3.62/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_12397,plain,
% 3.62/1.00      ( k5_enumset1(sK0,sK2,sK1,sK3,sK3,sK3,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_10246,c_17]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_14694,plain,
% 3.62/1.00      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK3,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_2404,c_12397]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3,plain,
% 3.62/1.00      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X1,X2) ),
% 3.62/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_22,plain,
% 3.62/1.00      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
% 3.62/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_183,plain,
% 3.62/1.00      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK3,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(contradiction,plain,
% 3.62/1.00      ( $false ),
% 3.62/1.00      inference(minisat,[status(thm)],[c_14694,c_183]) ).
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  ------                               Statistics
% 3.62/1.00  
% 3.62/1.00  ------ Selected
% 3.62/1.00  
% 3.62/1.00  total_time:                             0.5
% 3.62/1.00  
%------------------------------------------------------------------------------
