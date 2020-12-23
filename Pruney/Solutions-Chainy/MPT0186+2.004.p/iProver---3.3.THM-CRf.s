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
% DateTime   : Thu Dec  3 11:27:47 EST 2020

% Result     : Theorem 38.98s
% Output     : CNFRefutation 38.98s
% Verified   : 
% Statistics : Number of formulae       :  106 (6059 expanded)
%              Number of clauses        :   62 ( 683 expanded)
%              Number of leaves         :   16 (2017 expanded)
%              Depth                    :   22
%              Number of atoms          :  107 (6060 expanded)
%              Number of equality atoms :  106 (6059 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

fof(f35,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X0,X2) ),
    inference(definition_unfolding,[],[f31,f35,f35])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
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

fof(f36,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f37,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f22,f33,f28,f37])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f23,f33,f36])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X0,X0,X0,X1,X2)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f39])).

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

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f21,f33,f28,f28])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))),k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3))))))) ),
    inference(definition_unfolding,[],[f24,f33,f39,f36,f34])).

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
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3) ),
    inference(definition_unfolding,[],[f32,f28,f28])).

cnf(c_3,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_0,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X0,X0,X0,X1,X2)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1232,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_17,c_15])).

cnf(c_1238,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_14,c_1232])).

cnf(c_1295,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X1_36,X1_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1238,c_17])).

cnf(c_1246,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36) = k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36) ),
    inference(superposition,[status(thm)],[c_1232,c_14])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))),k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3))))))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))),k5_xboole_0(k3_enumset1(X6_36,X6_36,X6_36,X6_36,X7_36),k3_xboole_0(k3_enumset1(X6_36,X6_36,X6_36,X6_36,X7_36),k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36))))))) = k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X5_36,X6_36,X7_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X5_36,X6_36,X7_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1451,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36)))),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36))))))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_1246,c_16])).

cnf(c_1453,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
    inference(demodulation,[status(thm)],[c_1451,c_15,c_16])).

cnf(c_56226,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36)))),k3_xboole_0(k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36)))),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_xboole_0(k3_enumset1(X1_36,X0_36,X1_36,X3_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X1_36,X0_36,X1_36,X3_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_1295,c_1453])).

cnf(c_1244,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1232,c_15])).

cnf(c_1222,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_2346,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1244,c_1222])).

cnf(c_1249,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1232,c_17])).

cnf(c_1228,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_14,c_17])).

cnf(c_2717,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1249,c_1228])).

cnf(c_6289,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) = k3_enumset1(X1_36,X0_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_2346,c_2717])).

cnf(c_56254,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_xboole_0(k3_enumset1(X1_36,X0_36,X1_36,X2_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X1_36,X0_36,X1_36,X2_36,X2_36)))) ),
    inference(superposition,[status(thm)],[c_6289,c_1453])).

cnf(c_2350,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1244,c_17])).

cnf(c_1515,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_1222,c_15])).

cnf(c_2439,plain,
    ( k3_enumset1(X0_36,X1_36,X0_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2350,c_1515])).

cnf(c_2912,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X2_36)))) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_2439,c_15])).

cnf(c_56656,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56254,c_2912])).

cnf(c_2456,plain,
    ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2350,c_14])).

cnf(c_2596,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2456,c_1232])).

cnf(c_2716,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1249,c_17])).

cnf(c_4749,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X1_36,X1_36,X0_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2596,c_2716])).

cnf(c_56300,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X2_36,X2_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_4749,c_1453])).

cnf(c_56658,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k3_enumset1(X1_36,X0_36,X3_36,X2_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56656,c_56300])).

cnf(c_2441,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2350,c_1232])).

cnf(c_1253,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1232,c_14])).

cnf(c_1351,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1253,c_1232])).

cnf(c_3050,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X1_36,X0_36,X2_36,X2_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2441,c_1351])).

cnf(c_56283,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_3050,c_1453])).

cnf(c_56662,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56658,c_56283])).

cnf(c_1259,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1232,c_1232])).

cnf(c_3042,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2441,c_1259])).

cnf(c_56284,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_xboole_0(k3_enumset1(X1_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X1_36,X0_36,X1_36,X2_36,X3_36)))) ),
    inference(superposition,[status(thm)],[c_3042,c_1453])).

cnf(c_56669,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X3_36,X2_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56658,c_56284])).

cnf(c_1518,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X3_36) ),
    inference(superposition,[status(thm)],[c_1222,c_17])).

cnf(c_2444,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2350,c_1518])).

cnf(c_3168,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X1_36,X0_36,X2_36,X2_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2444,c_1259])).

cnf(c_56263,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_3168,c_1453])).

cnf(c_56672,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56669,c_56263])).

cnf(c_3176,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2444,c_1351])).

cnf(c_56260,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_3176,c_1453])).

cnf(c_56673,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k3_enumset1(X1_36,X0_36,X3_36,X2_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56669,c_56260])).

cnf(c_2599,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_2456,c_1518])).

cnf(c_56265,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
    inference(superposition,[status(thm)],[c_2599,c_1453])).

cnf(c_56682,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X3_36,X2_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56673,c_56265])).

cnf(c_56717,plain,
    ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X0_36,X1_36,X3_36,X2_36,X4_36) ),
    inference(demodulation,[status(thm)],[c_56226,c_56662,c_56672,c_56682])).

cnf(c_4,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_116981,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_56717,c_13])).

cnf(c_18,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_3551,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_116981,c_3551])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:01:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 38.98/5.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.98/5.48  
% 38.98/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 38.98/5.48  
% 38.98/5.48  ------  iProver source info
% 38.98/5.48  
% 38.98/5.48  git: date: 2020-06-30 10:37:57 +0100
% 38.98/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 38.98/5.48  git: non_committed_changes: false
% 38.98/5.48  git: last_make_outside_of_git: false
% 38.98/5.48  
% 38.98/5.48  ------ 
% 38.98/5.48  ------ Parsing...
% 38.98/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  ------ Proving...
% 38.98/5.48  ------ Problem Properties 
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  clauses                                 5
% 38.98/5.48  conjectures                             1
% 38.98/5.48  EPR                                     0
% 38.98/5.48  Horn                                    5
% 38.98/5.48  unary                                   5
% 38.98/5.48  binary                                  0
% 38.98/5.48  lits                                    5
% 38.98/5.48  lits eq                                 5
% 38.98/5.48  fd_pure                                 0
% 38.98/5.48  fd_pseudo                               0
% 38.98/5.48  fd_cond                                 0
% 38.98/5.48  fd_pseudo_cond                          0
% 38.98/5.48  AC symbols                              0
% 38.98/5.48  
% 38.98/5.48  ------ Input Options Time Limit: Unbounded
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing...
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 38.98/5.48  Current options:
% 38.98/5.48  ------ 
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing...
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing...
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 38.98/5.48  
% 38.98/5.48  ------ Proving...
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  % SZS status Theorem for theBenchmark.p
% 38.98/5.48  
% 38.98/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 38.98/5.48  
% 38.98/5.48  fof(f13,axiom,(
% 38.98/5.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f31,plain,(
% 38.98/5.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f13])).
% 38.98/5.48  
% 38.98/5.48  fof(f9,axiom,(
% 38.98/5.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f27,plain,(
% 38.98/5.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f9])).
% 38.98/5.48  
% 38.98/5.48  fof(f10,axiom,(
% 38.98/5.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f28,plain,(
% 38.98/5.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f10])).
% 38.98/5.48  
% 38.98/5.48  fof(f35,plain,(
% 38.98/5.48    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f27,f28])).
% 38.98/5.48  
% 38.98/5.48  fof(f43,plain,(
% 38.98/5.48    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X0,X2)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f31,f35,f35])).
% 38.98/5.48  
% 38.98/5.48  fof(f4,axiom,(
% 38.98/5.48    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f22,plain,(
% 38.98/5.48    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f4])).
% 38.98/5.48  
% 38.98/5.48  fof(f2,axiom,(
% 38.98/5.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f20,plain,(
% 38.98/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f2])).
% 38.98/5.48  
% 38.98/5.48  fof(f1,axiom,(
% 38.98/5.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f19,plain,(
% 38.98/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 38.98/5.48    inference(cnf_transformation,[],[f1])).
% 38.98/5.48  
% 38.98/5.48  fof(f33,plain,(
% 38.98/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f20,f19])).
% 38.98/5.48  
% 38.98/5.48  fof(f7,axiom,(
% 38.98/5.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f25,plain,(
% 38.98/5.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f7])).
% 38.98/5.48  
% 38.98/5.48  fof(f8,axiom,(
% 38.98/5.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f26,plain,(
% 38.98/5.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f8])).
% 38.98/5.48  
% 38.98/5.48  fof(f36,plain,(
% 38.98/5.48    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f26,f35])).
% 38.98/5.48  
% 38.98/5.48  fof(f37,plain,(
% 38.98/5.48    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f25,f36])).
% 38.98/5.48  
% 38.98/5.48  fof(f40,plain,(
% 38.98/5.48    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f22,f33,f28,f37])).
% 38.98/5.48  
% 38.98/5.48  fof(f11,axiom,(
% 38.98/5.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f29,plain,(
% 38.98/5.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f11])).
% 38.98/5.48  
% 38.98/5.48  fof(f12,axiom,(
% 38.98/5.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f30,plain,(
% 38.98/5.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f12])).
% 38.98/5.48  
% 38.98/5.48  fof(f5,axiom,(
% 38.98/5.48    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f23,plain,(
% 38.98/5.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f5])).
% 38.98/5.48  
% 38.98/5.48  fof(f38,plain,(
% 38.98/5.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_xboole_0(k3_enumset1(X5,X5,X5,X5,X6),k3_enumset1(X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f23,f33,f36])).
% 38.98/5.48  
% 38.98/5.48  fof(f39,plain,(
% 38.98/5.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f30,f38])).
% 38.98/5.48  
% 38.98/5.48  fof(f42,plain,(
% 38.98/5.48    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X0,X0,X0,X1,X2)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f29,f39])).
% 38.98/5.48  
% 38.98/5.48  fof(f6,axiom,(
% 38.98/5.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f24,plain,(
% 38.98/5.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f6])).
% 38.98/5.48  
% 38.98/5.48  fof(f3,axiom,(
% 38.98/5.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f21,plain,(
% 38.98/5.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 38.98/5.48    inference(cnf_transformation,[],[f3])).
% 38.98/5.48  
% 38.98/5.48  fof(f34,plain,(
% 38.98/5.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 38.98/5.48    inference(definition_unfolding,[],[f21,f33,f28,f28])).
% 38.98/5.48  
% 38.98/5.48  fof(f41,plain,(
% 38.98/5.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))),k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))))))) )),
% 38.98/5.48    inference(definition_unfolding,[],[f24,f33,f39,f36,f34])).
% 38.98/5.48  
% 38.98/5.48  fof(f14,conjecture,(
% 38.98/5.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 38.98/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.98/5.48  
% 38.98/5.48  fof(f15,negated_conjecture,(
% 38.98/5.48    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 38.98/5.48    inference(negated_conjecture,[],[f14])).
% 38.98/5.48  
% 38.98/5.48  fof(f16,plain,(
% 38.98/5.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 38.98/5.48    inference(ennf_transformation,[],[f15])).
% 38.98/5.48  
% 38.98/5.48  fof(f17,plain,(
% 38.98/5.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 38.98/5.48    introduced(choice_axiom,[])).
% 38.98/5.48  
% 38.98/5.48  fof(f18,plain,(
% 38.98/5.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 38.98/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 38.98/5.48  
% 38.98/5.48  fof(f32,plain,(
% 38.98/5.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 38.98/5.48    inference(cnf_transformation,[],[f18])).
% 38.98/5.48  
% 38.98/5.48  fof(f44,plain,(
% 38.98/5.48    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3)),
% 38.98/5.48    inference(definition_unfolding,[],[f32,f28,f28])).
% 38.98/5.48  
% 38.98/5.48  cnf(c_3,plain,
% 38.98/5.48      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X0,X2) ),
% 38.98/5.48      inference(cnf_transformation,[],[f43]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_14,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 38.98/5.48      inference(subtyping,[status(esa)],[c_3]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_0,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 38.98/5.48      inference(cnf_transformation,[],[f40]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_17,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(subtyping,[status(esa)],[c_0]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X0,X0,X0,X1,X2)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 38.98/5.48      inference(cnf_transformation,[],[f42]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_15,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(subtyping,[status(esa)],[c_2]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1232,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_17,c_15]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1238,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X1_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_14,c_1232]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1295,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X1_36,X1_36,X0_36,X1_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1238,c_17]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1246,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36) = k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1232,c_14]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1,plain,
% 38.98/5.48      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3)))),k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X7),k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X0,X0,X1,X2,X3))))))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
% 38.98/5.48      inference(cnf_transformation,[],[f41]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_16,plain,
% 38.98/5.48      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))),k5_xboole_0(k3_enumset1(X6_36,X6_36,X6_36,X6_36,X7_36),k3_xboole_0(k3_enumset1(X6_36,X6_36,X6_36,X6_36,X7_36),k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36))))))) = k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X5_36,X6_36,X7_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X5_36,X6_36,X7_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) ),
% 38.98/5.48      inference(subtyping,[status(esa)],[c_1]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1451,plain,
% 38.98/5.48      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36)))),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X0_36))))))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1246,c_16]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1453,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X5_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X4_36,X5_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_1451,c_15,c_16]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56226,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36)))),k3_xboole_0(k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36)))),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_xboole_0(k3_enumset1(X1_36,X0_36,X1_36,X3_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X1_36,X0_36,X1_36,X3_36,X2_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1295,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1244,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X1_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1232,c_15]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1222,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2346,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1244,c_1222]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1249,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1232,c_17]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1228,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_14,c_17]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2717,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1249,c_1228]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_6289,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) = k3_enumset1(X1_36,X0_36,X0_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2346,c_2717]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56254,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_xboole_0(k3_enumset1(X1_36,X0_36,X1_36,X2_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X1_36,X0_36,X1_36,X2_36,X2_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_6289,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2350,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1244,c_17]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1515,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1222,c_15]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2439,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X0_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2350,c_1515]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2912,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X2_36)))) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2439,c_15]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56656,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56254,c_2912]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2456,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X1_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2350,c_14]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2596,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2456,c_1232]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2716,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1249,c_17]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_4749,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X1_36,X1_36,X0_36,X0_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2596,c_2716]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56300,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X2_36,X2_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_4749,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56658,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k3_enumset1(X1_36,X0_36,X3_36,X2_36,X4_36) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56656,c_56300]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2441,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2350,c_1232]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1253,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1232,c_14]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1351,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1253,c_1232]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_3050,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X1_36,X0_36,X2_36,X2_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2441,c_1351]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56283,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_3050,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56662,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56658,c_56283]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1259,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1232,c_1232]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_3042,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X1_36,X2_36) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2441,c_1259]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56284,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_xboole_0(k3_enumset1(X1_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36),k3_enumset1(X1_36,X0_36,X1_36,X2_36,X3_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_3042,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56669,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X3_36,X2_36,X4_36) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56658,c_56284]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_1518,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X3_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_1222,c_17]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2444,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2350,c_1518]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_3168,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X1_36,X0_36,X2_36,X2_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2444,c_1259]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56263,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X3_36,X2_36,X4_36,X4_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_3168,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56672,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k3_enumset1(X1_36,X0_36,X2_36,X3_36,X4_36) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56669,c_56263]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_3176,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X0_36,X1_36,X2_36,X2_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2444,c_1351]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56260,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X3_36,X4_36,X4_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_3176,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56673,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k3_enumset1(X1_36,X0_36,X3_36,X2_36,X4_36) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56669,c_56260]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_2599,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X0_36,X1_36,X0_36,X2_36) = k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2456,c_1518]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56265,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X4_36),k3_enumset1(X0_36,X1_36,X0_36,X2_36,X3_36)))) = k5_xboole_0(k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36)))) ),
% 38.98/5.48      inference(superposition,[status(thm)],[c_2599,c_1453]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56682,plain,
% 38.98/5.48      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X3_36,X4_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X0_36,X1_36,X3_36,X2_36,X4_36) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56673,c_56265]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_56717,plain,
% 38.98/5.48      ( k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) = k3_enumset1(X0_36,X1_36,X3_36,X2_36,X4_36) ),
% 38.98/5.48      inference(demodulation,
% 38.98/5.48                [status(thm)],
% 38.98/5.48                [c_56226,c_56662,c_56672,c_56682]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_4,negated_conjecture,
% 38.98/5.48      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3) ),
% 38.98/5.48      inference(cnf_transformation,[],[f44]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_13,negated_conjecture,
% 38.98/5.48      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3) ),
% 38.98/5.48      inference(subtyping,[status(esa)],[c_4]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_116981,plain,
% 38.98/5.48      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 38.98/5.48      inference(demodulation,[status(thm)],[c_56717,c_13]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_18,plain,( X0_35 = X0_35 ),theory(equality) ).
% 38.98/5.48  
% 38.98/5.48  cnf(c_3551,plain,
% 38.98/5.48      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 38.98/5.48      inference(instantiation,[status(thm)],[c_18]) ).
% 38.98/5.48  
% 38.98/5.48  cnf(contradiction,plain,
% 38.98/5.48      ( $false ),
% 38.98/5.48      inference(minisat,[status(thm)],[c_116981,c_3551]) ).
% 38.98/5.48  
% 38.98/5.48  
% 38.98/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 38.98/5.48  
% 38.98/5.48  ------                               Statistics
% 38.98/5.48  
% 38.98/5.48  ------ Selected
% 38.98/5.48  
% 38.98/5.48  total_time:                             4.522
% 38.98/5.48  
%------------------------------------------------------------------------------
