%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:26 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 953 expanded)
%              Number of clauses        :   41 ( 112 expanded)
%              Number of leaves         :   15 ( 338 expanded)
%              Depth                    :   15
%              Number of atoms          :   85 ( 954 expanded)
%              Number of equality atoms :   84 ( 953 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f43,f38,f38])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f33,f43,f47,f44])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f43,f38])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f44,f45])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) ),
    inference(definition_unfolding,[],[f28,f44,f44])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X1,X1,X3),k5_xboole_0(k1_enumset1(X2,X2,X0),k3_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X3)))) ),
    inference(definition_unfolding,[],[f29,f44,f44])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2)))) ),
    inference(definition_unfolding,[],[f31,f44,f44])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f42,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f42,f43,f38,f38])).

cnf(c_6,plain,
    ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k3_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k1_enumset1(X0_35,X1_35,X2_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X1_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_57,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_21,c_28])).

cnf(c_58,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_21,c_21])).

cnf(c_59,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(demodulation,[status(thm)],[c_57,c_58])).

cnf(c_92,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_22,c_59])).

cnf(c_330,plain,
    ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X0_35,X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_92,c_28])).

cnf(c_397,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_330,c_22])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_253,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_22,c_26])).

cnf(c_3,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X0),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X3_35,X3_35,X0_35)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_221,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_25,c_22])).

cnf(c_5,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X3_35,X3_35,X2_35)))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_127,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_23,c_22])).

cnf(c_130,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X1_35,X0_35) ),
    inference(light_normalisation,[status(thm)],[c_127,c_28])).

cnf(c_226,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X1_35,X0_35,X2_35) ),
    inference(light_normalisation,[status(thm)],[c_221,c_130])).

cnf(c_288,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
    inference(light_normalisation,[status(thm)],[c_253,c_226])).

cnf(c_417,plain,
    ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X2_35,X0_35) ),
    inference(light_normalisation,[status(thm)],[c_397,c_92,c_288])).

cnf(c_195,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_22,c_25])).

cnf(c_208,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_25,c_22])).

cnf(c_224,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_25,c_59])).

cnf(c_228,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
    inference(demodulation,[status(thm)],[c_208,c_224])).

cnf(c_229,plain,
    ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X0_35,X2_35) ),
    inference(demodulation,[status(thm)],[c_195,c_226,c_228])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_27,plain,
    ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_40,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK0,sK2,sK0),k1_enumset1(sK1,sK1,sK1)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_21,c_19])).

cnf(c_42,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_27,c_40])).

cnf(c_289,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_229,c_42])).

cnf(c_498,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_417,c_289])).

cnf(c_43,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_27,c_28])).

cnf(c_499,plain,
    ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_498,c_43])).

cnf(c_500,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_499])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.84/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.01  
% 1.84/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.84/1.01  
% 1.84/1.01  ------  iProver source info
% 1.84/1.01  
% 1.84/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.84/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.84/1.01  git: non_committed_changes: false
% 1.84/1.01  git: last_make_outside_of_git: false
% 1.84/1.01  
% 1.84/1.01  ------ 
% 1.84/1.01  
% 1.84/1.01  ------ Input Options
% 1.84/1.01  
% 1.84/1.01  --out_options                           all
% 1.84/1.01  --tptp_safe_out                         true
% 1.84/1.01  --problem_path                          ""
% 1.84/1.01  --include_path                          ""
% 1.84/1.01  --clausifier                            res/vclausify_rel
% 1.84/1.01  --clausifier_options                    --mode clausify
% 1.84/1.01  --stdin                                 false
% 1.84/1.01  --stats_out                             all
% 1.84/1.01  
% 1.84/1.01  ------ General Options
% 1.84/1.01  
% 1.84/1.01  --fof                                   false
% 1.84/1.01  --time_out_real                         305.
% 1.84/1.01  --time_out_virtual                      -1.
% 1.84/1.01  --symbol_type_check                     false
% 1.84/1.01  --clausify_out                          false
% 1.84/1.01  --sig_cnt_out                           false
% 1.84/1.01  --trig_cnt_out                          false
% 1.84/1.01  --trig_cnt_out_tolerance                1.
% 1.84/1.01  --trig_cnt_out_sk_spl                   false
% 1.84/1.01  --abstr_cl_out                          false
% 1.84/1.01  
% 1.84/1.01  ------ Global Options
% 1.84/1.01  
% 1.84/1.01  --schedule                              default
% 1.84/1.01  --add_important_lit                     false
% 1.84/1.01  --prop_solver_per_cl                    1000
% 1.84/1.01  --min_unsat_core                        false
% 1.84/1.01  --soft_assumptions                      false
% 1.84/1.01  --soft_lemma_size                       3
% 1.84/1.01  --prop_impl_unit_size                   0
% 1.84/1.01  --prop_impl_unit                        []
% 1.84/1.01  --share_sel_clauses                     true
% 1.84/1.01  --reset_solvers                         false
% 1.84/1.01  --bc_imp_inh                            [conj_cone]
% 1.84/1.01  --conj_cone_tolerance                   3.
% 1.84/1.01  --extra_neg_conj                        none
% 1.84/1.01  --large_theory_mode                     true
% 1.84/1.01  --prolific_symb_bound                   200
% 1.84/1.01  --lt_threshold                          2000
% 1.84/1.01  --clause_weak_htbl                      true
% 1.84/1.01  --gc_record_bc_elim                     false
% 1.84/1.01  
% 1.84/1.01  ------ Preprocessing Options
% 1.84/1.01  
% 1.84/1.01  --preprocessing_flag                    true
% 1.84/1.01  --time_out_prep_mult                    0.1
% 1.84/1.01  --splitting_mode                        input
% 1.84/1.01  --splitting_grd                         true
% 1.84/1.01  --splitting_cvd                         false
% 1.84/1.01  --splitting_cvd_svl                     false
% 1.84/1.01  --splitting_nvd                         32
% 1.84/1.01  --sub_typing                            true
% 1.84/1.01  --prep_gs_sim                           true
% 1.84/1.01  --prep_unflatten                        true
% 1.84/1.01  --prep_res_sim                          true
% 1.84/1.01  --prep_upred                            true
% 1.84/1.01  --prep_sem_filter                       exhaustive
% 1.84/1.01  --prep_sem_filter_out                   false
% 1.84/1.01  --pred_elim                             true
% 1.84/1.01  --res_sim_input                         true
% 1.84/1.01  --eq_ax_congr_red                       true
% 1.84/1.01  --pure_diseq_elim                       true
% 1.84/1.01  --brand_transform                       false
% 1.84/1.01  --non_eq_to_eq                          false
% 1.84/1.01  --prep_def_merge                        true
% 1.84/1.01  --prep_def_merge_prop_impl              false
% 1.84/1.01  --prep_def_merge_mbd                    true
% 1.84/1.01  --prep_def_merge_tr_red                 false
% 1.84/1.01  --prep_def_merge_tr_cl                  false
% 1.84/1.01  --smt_preprocessing                     true
% 1.84/1.01  --smt_ac_axioms                         fast
% 1.84/1.01  --preprocessed_out                      false
% 1.84/1.01  --preprocessed_stats                    false
% 1.84/1.01  
% 1.84/1.01  ------ Abstraction refinement Options
% 1.84/1.01  
% 1.84/1.01  --abstr_ref                             []
% 1.84/1.01  --abstr_ref_prep                        false
% 1.84/1.01  --abstr_ref_until_sat                   false
% 1.84/1.01  --abstr_ref_sig_restrict                funpre
% 1.84/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/1.01  --abstr_ref_under                       []
% 1.84/1.01  
% 1.84/1.01  ------ SAT Options
% 1.84/1.01  
% 1.84/1.01  --sat_mode                              false
% 1.84/1.01  --sat_fm_restart_options                ""
% 1.84/1.01  --sat_gr_def                            false
% 1.84/1.01  --sat_epr_types                         true
% 1.84/1.01  --sat_non_cyclic_types                  false
% 1.84/1.01  --sat_finite_models                     false
% 1.84/1.01  --sat_fm_lemmas                         false
% 1.84/1.01  --sat_fm_prep                           false
% 1.84/1.01  --sat_fm_uc_incr                        true
% 1.84/1.01  --sat_out_model                         small
% 1.84/1.01  --sat_out_clauses                       false
% 1.84/1.01  
% 1.84/1.01  ------ QBF Options
% 1.84/1.01  
% 1.84/1.01  --qbf_mode                              false
% 1.84/1.01  --qbf_elim_univ                         false
% 1.84/1.01  --qbf_dom_inst                          none
% 1.84/1.01  --qbf_dom_pre_inst                      false
% 1.84/1.01  --qbf_sk_in                             false
% 1.84/1.01  --qbf_pred_elim                         true
% 1.84/1.01  --qbf_split                             512
% 1.84/1.01  
% 1.84/1.01  ------ BMC1 Options
% 1.84/1.01  
% 1.84/1.01  --bmc1_incremental                      false
% 1.84/1.01  --bmc1_axioms                           reachable_all
% 1.84/1.01  --bmc1_min_bound                        0
% 1.84/1.01  --bmc1_max_bound                        -1
% 1.84/1.01  --bmc1_max_bound_default                -1
% 1.84/1.01  --bmc1_symbol_reachability              true
% 1.84/1.01  --bmc1_property_lemmas                  false
% 1.84/1.01  --bmc1_k_induction                      false
% 1.84/1.01  --bmc1_non_equiv_states                 false
% 1.84/1.01  --bmc1_deadlock                         false
% 1.84/1.01  --bmc1_ucm                              false
% 1.84/1.01  --bmc1_add_unsat_core                   none
% 1.84/1.01  --bmc1_unsat_core_children              false
% 1.84/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/1.01  --bmc1_out_stat                         full
% 1.84/1.01  --bmc1_ground_init                      false
% 1.84/1.01  --bmc1_pre_inst_next_state              false
% 1.84/1.01  --bmc1_pre_inst_state                   false
% 1.84/1.01  --bmc1_pre_inst_reach_state             false
% 1.84/1.01  --bmc1_out_unsat_core                   false
% 1.84/1.01  --bmc1_aig_witness_out                  false
% 1.84/1.01  --bmc1_verbose                          false
% 1.84/1.01  --bmc1_dump_clauses_tptp                false
% 1.84/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.84/1.01  --bmc1_dump_file                        -
% 1.84/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.84/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.84/1.01  --bmc1_ucm_extend_mode                  1
% 1.84/1.01  --bmc1_ucm_init_mode                    2
% 1.84/1.01  --bmc1_ucm_cone_mode                    none
% 1.84/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.84/1.01  --bmc1_ucm_relax_model                  4
% 1.84/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.84/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/1.01  --bmc1_ucm_layered_model                none
% 1.84/1.02  --bmc1_ucm_max_lemma_size               10
% 1.84/1.02  
% 1.84/1.02  ------ AIG Options
% 1.84/1.02  
% 1.84/1.02  --aig_mode                              false
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation Options
% 1.84/1.02  
% 1.84/1.02  --instantiation_flag                    true
% 1.84/1.02  --inst_sos_flag                         false
% 1.84/1.02  --inst_sos_phase                        true
% 1.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel_side                     num_symb
% 1.84/1.02  --inst_solver_per_active                1400
% 1.84/1.02  --inst_solver_calls_frac                1.
% 1.84/1.02  --inst_passive_queue_type               priority_queues
% 1.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/1.02  --inst_passive_queues_freq              [25;2]
% 1.84/1.02  --inst_dismatching                      true
% 1.84/1.02  --inst_eager_unprocessed_to_passive     true
% 1.84/1.02  --inst_prop_sim_given                   true
% 1.84/1.02  --inst_prop_sim_new                     false
% 1.84/1.02  --inst_subs_new                         false
% 1.84/1.02  --inst_eq_res_simp                      false
% 1.84/1.02  --inst_subs_given                       false
% 1.84/1.02  --inst_orphan_elimination               true
% 1.84/1.02  --inst_learning_loop_flag               true
% 1.84/1.02  --inst_learning_start                   3000
% 1.84/1.02  --inst_learning_factor                  2
% 1.84/1.02  --inst_start_prop_sim_after_learn       3
% 1.84/1.02  --inst_sel_renew                        solver
% 1.84/1.02  --inst_lit_activity_flag                true
% 1.84/1.02  --inst_restr_to_given                   false
% 1.84/1.02  --inst_activity_threshold               500
% 1.84/1.02  --inst_out_proof                        true
% 1.84/1.02  
% 1.84/1.02  ------ Resolution Options
% 1.84/1.02  
% 1.84/1.02  --resolution_flag                       true
% 1.84/1.02  --res_lit_sel                           adaptive
% 1.84/1.02  --res_lit_sel_side                      none
% 1.84/1.02  --res_ordering                          kbo
% 1.84/1.02  --res_to_prop_solver                    active
% 1.84/1.02  --res_prop_simpl_new                    false
% 1.84/1.02  --res_prop_simpl_given                  true
% 1.84/1.02  --res_passive_queue_type                priority_queues
% 1.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/1.02  --res_passive_queues_freq               [15;5]
% 1.84/1.02  --res_forward_subs                      full
% 1.84/1.02  --res_backward_subs                     full
% 1.84/1.02  --res_forward_subs_resolution           true
% 1.84/1.02  --res_backward_subs_resolution          true
% 1.84/1.02  --res_orphan_elimination                true
% 1.84/1.02  --res_time_limit                        2.
% 1.84/1.02  --res_out_proof                         true
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Options
% 1.84/1.02  
% 1.84/1.02  --superposition_flag                    true
% 1.84/1.02  --sup_passive_queue_type                priority_queues
% 1.84/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.84/1.02  --demod_completeness_check              fast
% 1.84/1.02  --demod_use_ground                      true
% 1.84/1.02  --sup_to_prop_solver                    passive
% 1.84/1.02  --sup_prop_simpl_new                    true
% 1.84/1.02  --sup_prop_simpl_given                  true
% 1.84/1.02  --sup_fun_splitting                     false
% 1.84/1.02  --sup_smt_interval                      50000
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Simplification Setup
% 1.84/1.02  
% 1.84/1.02  --sup_indices_passive                   []
% 1.84/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_full_bw                           [BwDemod]
% 1.84/1.02  --sup_immed_triv                        [TrivRules]
% 1.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_immed_bw_main                     []
% 1.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  
% 1.84/1.02  ------ Combination Options
% 1.84/1.02  
% 1.84/1.02  --comb_res_mult                         3
% 1.84/1.02  --comb_sup_mult                         2
% 1.84/1.02  --comb_inst_mult                        10
% 1.84/1.02  
% 1.84/1.02  ------ Debug Options
% 1.84/1.02  
% 1.84/1.02  --dbg_backtrace                         false
% 1.84/1.02  --dbg_dump_prop_clauses                 false
% 1.84/1.02  --dbg_dump_prop_clauses_file            -
% 1.84/1.02  --dbg_out_stat                          false
% 1.84/1.02  ------ Parsing...
% 1.84/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.84/1.02  ------ Proving...
% 1.84/1.02  ------ Problem Properties 
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  clauses                                 10
% 1.84/1.02  conjectures                             1
% 1.84/1.02  EPR                                     0
% 1.84/1.02  Horn                                    10
% 1.84/1.02  unary                                   10
% 1.84/1.02  binary                                  0
% 1.84/1.02  lits                                    10
% 1.84/1.02  lits eq                                 10
% 1.84/1.02  fd_pure                                 0
% 1.84/1.02  fd_pseudo                               0
% 1.84/1.02  fd_cond                                 0
% 1.84/1.02  fd_pseudo_cond                          0
% 1.84/1.02  AC symbols                              0
% 1.84/1.02  
% 1.84/1.02  ------ Schedule UEQ
% 1.84/1.02  
% 1.84/1.02  ------ pure equality problem: resolution off 
% 1.84/1.02  
% 1.84/1.02  ------ Option_UEQ Time Limit: Unbounded
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  ------ 
% 1.84/1.02  Current options:
% 1.84/1.02  ------ 
% 1.84/1.02  
% 1.84/1.02  ------ Input Options
% 1.84/1.02  
% 1.84/1.02  --out_options                           all
% 1.84/1.02  --tptp_safe_out                         true
% 1.84/1.02  --problem_path                          ""
% 1.84/1.02  --include_path                          ""
% 1.84/1.02  --clausifier                            res/vclausify_rel
% 1.84/1.02  --clausifier_options                    --mode clausify
% 1.84/1.02  --stdin                                 false
% 1.84/1.02  --stats_out                             all
% 1.84/1.02  
% 1.84/1.02  ------ General Options
% 1.84/1.02  
% 1.84/1.02  --fof                                   false
% 1.84/1.02  --time_out_real                         305.
% 1.84/1.02  --time_out_virtual                      -1.
% 1.84/1.02  --symbol_type_check                     false
% 1.84/1.02  --clausify_out                          false
% 1.84/1.02  --sig_cnt_out                           false
% 1.84/1.02  --trig_cnt_out                          false
% 1.84/1.02  --trig_cnt_out_tolerance                1.
% 1.84/1.02  --trig_cnt_out_sk_spl                   false
% 1.84/1.02  --abstr_cl_out                          false
% 1.84/1.02  
% 1.84/1.02  ------ Global Options
% 1.84/1.02  
% 1.84/1.02  --schedule                              default
% 1.84/1.02  --add_important_lit                     false
% 1.84/1.02  --prop_solver_per_cl                    1000
% 1.84/1.02  --min_unsat_core                        false
% 1.84/1.02  --soft_assumptions                      false
% 1.84/1.02  --soft_lemma_size                       3
% 1.84/1.02  --prop_impl_unit_size                   0
% 1.84/1.02  --prop_impl_unit                        []
% 1.84/1.02  --share_sel_clauses                     true
% 1.84/1.02  --reset_solvers                         false
% 1.84/1.02  --bc_imp_inh                            [conj_cone]
% 1.84/1.02  --conj_cone_tolerance                   3.
% 1.84/1.02  --extra_neg_conj                        none
% 1.84/1.02  --large_theory_mode                     true
% 1.84/1.02  --prolific_symb_bound                   200
% 1.84/1.02  --lt_threshold                          2000
% 1.84/1.02  --clause_weak_htbl                      true
% 1.84/1.02  --gc_record_bc_elim                     false
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing Options
% 1.84/1.02  
% 1.84/1.02  --preprocessing_flag                    true
% 1.84/1.02  --time_out_prep_mult                    0.1
% 1.84/1.02  --splitting_mode                        input
% 1.84/1.02  --splitting_grd                         true
% 1.84/1.02  --splitting_cvd                         false
% 1.84/1.02  --splitting_cvd_svl                     false
% 1.84/1.02  --splitting_nvd                         32
% 1.84/1.02  --sub_typing                            true
% 1.84/1.02  --prep_gs_sim                           true
% 1.84/1.02  --prep_unflatten                        true
% 1.84/1.02  --prep_res_sim                          true
% 1.84/1.02  --prep_upred                            true
% 1.84/1.02  --prep_sem_filter                       exhaustive
% 1.84/1.02  --prep_sem_filter_out                   false
% 1.84/1.02  --pred_elim                             true
% 1.84/1.02  --res_sim_input                         true
% 1.84/1.02  --eq_ax_congr_red                       true
% 1.84/1.02  --pure_diseq_elim                       true
% 1.84/1.02  --brand_transform                       false
% 1.84/1.02  --non_eq_to_eq                          false
% 1.84/1.02  --prep_def_merge                        true
% 1.84/1.02  --prep_def_merge_prop_impl              false
% 1.84/1.02  --prep_def_merge_mbd                    true
% 1.84/1.02  --prep_def_merge_tr_red                 false
% 1.84/1.02  --prep_def_merge_tr_cl                  false
% 1.84/1.02  --smt_preprocessing                     true
% 1.84/1.02  --smt_ac_axioms                         fast
% 1.84/1.02  --preprocessed_out                      false
% 1.84/1.02  --preprocessed_stats                    false
% 1.84/1.02  
% 1.84/1.02  ------ Abstraction refinement Options
% 1.84/1.02  
% 1.84/1.02  --abstr_ref                             []
% 1.84/1.02  --abstr_ref_prep                        false
% 1.84/1.02  --abstr_ref_until_sat                   false
% 1.84/1.02  --abstr_ref_sig_restrict                funpre
% 1.84/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/1.02  --abstr_ref_under                       []
% 1.84/1.02  
% 1.84/1.02  ------ SAT Options
% 1.84/1.02  
% 1.84/1.02  --sat_mode                              false
% 1.84/1.02  --sat_fm_restart_options                ""
% 1.84/1.02  --sat_gr_def                            false
% 1.84/1.02  --sat_epr_types                         true
% 1.84/1.02  --sat_non_cyclic_types                  false
% 1.84/1.02  --sat_finite_models                     false
% 1.84/1.02  --sat_fm_lemmas                         false
% 1.84/1.02  --sat_fm_prep                           false
% 1.84/1.02  --sat_fm_uc_incr                        true
% 1.84/1.02  --sat_out_model                         small
% 1.84/1.02  --sat_out_clauses                       false
% 1.84/1.02  
% 1.84/1.02  ------ QBF Options
% 1.84/1.02  
% 1.84/1.02  --qbf_mode                              false
% 1.84/1.02  --qbf_elim_univ                         false
% 1.84/1.02  --qbf_dom_inst                          none
% 1.84/1.02  --qbf_dom_pre_inst                      false
% 1.84/1.02  --qbf_sk_in                             false
% 1.84/1.02  --qbf_pred_elim                         true
% 1.84/1.02  --qbf_split                             512
% 1.84/1.02  
% 1.84/1.02  ------ BMC1 Options
% 1.84/1.02  
% 1.84/1.02  --bmc1_incremental                      false
% 1.84/1.02  --bmc1_axioms                           reachable_all
% 1.84/1.02  --bmc1_min_bound                        0
% 1.84/1.02  --bmc1_max_bound                        -1
% 1.84/1.02  --bmc1_max_bound_default                -1
% 1.84/1.02  --bmc1_symbol_reachability              true
% 1.84/1.02  --bmc1_property_lemmas                  false
% 1.84/1.02  --bmc1_k_induction                      false
% 1.84/1.02  --bmc1_non_equiv_states                 false
% 1.84/1.02  --bmc1_deadlock                         false
% 1.84/1.02  --bmc1_ucm                              false
% 1.84/1.02  --bmc1_add_unsat_core                   none
% 1.84/1.02  --bmc1_unsat_core_children              false
% 1.84/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/1.02  --bmc1_out_stat                         full
% 1.84/1.02  --bmc1_ground_init                      false
% 1.84/1.02  --bmc1_pre_inst_next_state              false
% 1.84/1.02  --bmc1_pre_inst_state                   false
% 1.84/1.02  --bmc1_pre_inst_reach_state             false
% 1.84/1.02  --bmc1_out_unsat_core                   false
% 1.84/1.02  --bmc1_aig_witness_out                  false
% 1.84/1.02  --bmc1_verbose                          false
% 1.84/1.02  --bmc1_dump_clauses_tptp                false
% 1.84/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.84/1.02  --bmc1_dump_file                        -
% 1.84/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.84/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.84/1.02  --bmc1_ucm_extend_mode                  1
% 1.84/1.02  --bmc1_ucm_init_mode                    2
% 1.84/1.02  --bmc1_ucm_cone_mode                    none
% 1.84/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.84/1.02  --bmc1_ucm_relax_model                  4
% 1.84/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.84/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/1.02  --bmc1_ucm_layered_model                none
% 1.84/1.02  --bmc1_ucm_max_lemma_size               10
% 1.84/1.02  
% 1.84/1.02  ------ AIG Options
% 1.84/1.02  
% 1.84/1.02  --aig_mode                              false
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation Options
% 1.84/1.02  
% 1.84/1.02  --instantiation_flag                    false
% 1.84/1.02  --inst_sos_flag                         false
% 1.84/1.02  --inst_sos_phase                        true
% 1.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel_side                     num_symb
% 1.84/1.02  --inst_solver_per_active                1400
% 1.84/1.02  --inst_solver_calls_frac                1.
% 1.84/1.02  --inst_passive_queue_type               priority_queues
% 1.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/1.02  --inst_passive_queues_freq              [25;2]
% 1.84/1.02  --inst_dismatching                      true
% 1.84/1.02  --inst_eager_unprocessed_to_passive     true
% 1.84/1.02  --inst_prop_sim_given                   true
% 1.84/1.02  --inst_prop_sim_new                     false
% 1.84/1.02  --inst_subs_new                         false
% 1.84/1.02  --inst_eq_res_simp                      false
% 1.84/1.02  --inst_subs_given                       false
% 1.84/1.02  --inst_orphan_elimination               true
% 1.84/1.02  --inst_learning_loop_flag               true
% 1.84/1.02  --inst_learning_start                   3000
% 1.84/1.02  --inst_learning_factor                  2
% 1.84/1.02  --inst_start_prop_sim_after_learn       3
% 1.84/1.02  --inst_sel_renew                        solver
% 1.84/1.02  --inst_lit_activity_flag                true
% 1.84/1.02  --inst_restr_to_given                   false
% 1.84/1.02  --inst_activity_threshold               500
% 1.84/1.02  --inst_out_proof                        true
% 1.84/1.02  
% 1.84/1.02  ------ Resolution Options
% 1.84/1.02  
% 1.84/1.02  --resolution_flag                       false
% 1.84/1.02  --res_lit_sel                           adaptive
% 1.84/1.02  --res_lit_sel_side                      none
% 1.84/1.02  --res_ordering                          kbo
% 1.84/1.02  --res_to_prop_solver                    active
% 1.84/1.02  --res_prop_simpl_new                    false
% 1.84/1.02  --res_prop_simpl_given                  true
% 1.84/1.02  --res_passive_queue_type                priority_queues
% 1.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/1.02  --res_passive_queues_freq               [15;5]
% 1.84/1.02  --res_forward_subs                      full
% 1.84/1.02  --res_backward_subs                     full
% 1.84/1.02  --res_forward_subs_resolution           true
% 1.84/1.02  --res_backward_subs_resolution          true
% 1.84/1.02  --res_orphan_elimination                true
% 1.84/1.02  --res_time_limit                        2.
% 1.84/1.02  --res_out_proof                         true
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Options
% 1.84/1.02  
% 1.84/1.02  --superposition_flag                    true
% 1.84/1.02  --sup_passive_queue_type                priority_queues
% 1.84/1.02  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.84/1.02  --demod_completeness_check              fast
% 1.84/1.02  --demod_use_ground                      true
% 1.84/1.02  --sup_to_prop_solver                    active
% 1.84/1.02  --sup_prop_simpl_new                    false
% 1.84/1.02  --sup_prop_simpl_given                  false
% 1.84/1.02  --sup_fun_splitting                     true
% 1.84/1.02  --sup_smt_interval                      10000
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Simplification Setup
% 1.84/1.02  
% 1.84/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 1.84/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_full_triv                         [TrivRules]
% 1.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 1.84/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 1.84/1.02  --sup_immed_triv                        [TrivRules]
% 1.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_immed_bw_main                     []
% 1.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 1.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption]
% 1.84/1.02  
% 1.84/1.02  ------ Combination Options
% 1.84/1.02  
% 1.84/1.02  --comb_res_mult                         1
% 1.84/1.02  --comb_sup_mult                         1
% 1.84/1.02  --comb_inst_mult                        1000000
% 1.84/1.02  
% 1.84/1.02  ------ Debug Options
% 1.84/1.02  
% 1.84/1.02  --dbg_backtrace                         false
% 1.84/1.02  --dbg_dump_prop_clauses                 false
% 1.84/1.02  --dbg_dump_prop_clauses_file            -
% 1.84/1.02  --dbg_out_stat                          false
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  ------ Proving...
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  % SZS status Theorem for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02   Resolution empty clause
% 1.84/1.02  
% 1.84/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  fof(f10,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f33,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f10])).
% 1.84/1.02  
% 1.84/1.02  fof(f14,axiom,(
% 1.84/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f37,plain,(
% 1.84/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f14])).
% 1.84/1.02  
% 1.84/1.02  fof(f47,plain,(
% 1.84/1.02    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 1.84/1.02    inference(definition_unfolding,[],[f37,f38])).
% 1.84/1.02  
% 1.84/1.02  fof(f4,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f27,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f4])).
% 1.84/1.02  
% 1.84/1.02  fof(f3,axiom,(
% 1.84/1.02    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f26,plain,(
% 1.84/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f3])).
% 1.84/1.02  
% 1.84/1.02  fof(f2,axiom,(
% 1.84/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f25,plain,(
% 1.84/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.84/1.02    inference(cnf_transformation,[],[f2])).
% 1.84/1.02  
% 1.84/1.02  fof(f43,plain,(
% 1.84/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 1.84/1.02    inference(definition_unfolding,[],[f26,f25])).
% 1.84/1.02  
% 1.84/1.02  fof(f15,axiom,(
% 1.84/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f38,plain,(
% 1.84/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f15])).
% 1.84/1.02  
% 1.84/1.02  fof(f44,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.84/1.02    inference(definition_unfolding,[],[f27,f43,f38,f38])).
% 1.84/1.02  
% 1.84/1.02  fof(f55,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2))))) )),
% 1.84/1.02    inference(definition_unfolding,[],[f33,f43,f47,f44])).
% 1.84/1.02  
% 1.84/1.02  fof(f17,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f40,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f17])).
% 1.84/1.02  
% 1.84/1.02  fof(f11,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f34,plain,(
% 1.84/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f11])).
% 1.84/1.02  
% 1.84/1.02  fof(f45,plain,(
% 1.84/1.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.84/1.02    inference(definition_unfolding,[],[f34,f43,f38])).
% 1.84/1.02  
% 1.84/1.02  fof(f56,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))))) )),
% 1.84/1.02    inference(definition_unfolding,[],[f40,f44,f45])).
% 1.84/1.02  
% 1.84/1.02  fof(f16,axiom,(
% 1.84/1.02    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f39,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f16])).
% 1.84/1.02  
% 1.84/1.02  fof(f50,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 1.84/1.02    inference(definition_unfolding,[],[f39,f44])).
% 1.84/1.02  
% 1.84/1.02  fof(f5,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f28,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f5])).
% 1.84/1.02  
% 1.84/1.02  fof(f51,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))))) )),
% 1.84/1.02    inference(definition_unfolding,[],[f28,f44,f44])).
% 1.84/1.02  
% 1.84/1.02  fof(f6,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f29,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f6])).
% 1.84/1.02  
% 1.84/1.02  fof(f52,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X1,X1,X3),k5_xboole_0(k1_enumset1(X2,X2,X0),k3_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X3))))) )),
% 1.84/1.02    inference(definition_unfolding,[],[f29,f44,f44])).
% 1.84/1.02  
% 1.84/1.02  fof(f8,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f31,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f8])).
% 1.84/1.02  
% 1.84/1.02  fof(f54,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2))))) )),
% 1.84/1.02    inference(definition_unfolding,[],[f31,f44,f44])).
% 1.84/1.02  
% 1.84/1.02  fof(f1,axiom,(
% 1.84/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f24,plain,(
% 1.84/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f1])).
% 1.84/1.02  
% 1.84/1.02  fof(f19,conjecture,(
% 1.84/1.02    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f20,negated_conjecture,(
% 1.84/1.02    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 1.84/1.02    inference(negated_conjecture,[],[f19])).
% 1.84/1.02  
% 1.84/1.02  fof(f21,plain,(
% 1.84/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 1.84/1.02    inference(ennf_transformation,[],[f20])).
% 1.84/1.02  
% 1.84/1.02  fof(f22,plain,(
% 1.84/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f23,plain,(
% 1.84/1.02    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 1.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 1.84/1.02  
% 1.84/1.02  fof(f42,plain,(
% 1.84/1.02    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f23])).
% 1.84/1.02  
% 1.84/1.02  fof(f58,plain,(
% 1.84/1.02    k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2)),
% 1.84/1.02    inference(definition_unfolding,[],[f42,f43,f38,f38])).
% 1.84/1.02  
% 1.84/1.02  cnf(c_6,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_22,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k3_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k1_enumset1(X0_35,X1_35,X2_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_7,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_21,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X1_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_0,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_28,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_57,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_21,c_28]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_58,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_21,c_21]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_59,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_57,c_58]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_92,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_22,c_59]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_330,plain,
% 1.84/1.02      ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X0_35,X0_35,X1_35) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_92,c_28]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_397,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_330,c_22]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_2,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_26,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_253,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_22,c_26]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X0),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0)))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_25,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X3_35,X3_35,X0_35)))) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_221,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_25,c_22]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_5,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2)))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_23,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X3_35,X3_35,X2_35)))) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_127,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_23,c_22]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_130,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X1_35,X0_35) ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_127,c_28]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_226,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X1_35,X0_35,X2_35) ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_221,c_130]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_288,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_253,c_226]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_417,plain,
% 1.84/1.02      ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X2_35,X0_35) ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_397,c_92,c_288]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_195,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_22,c_25]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_208,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_25,c_22]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_224,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_25,c_59]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_228,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_208,c_224]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_229,plain,
% 1.84/1.02      ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X0_35,X2_35) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_195,c_226,c_228]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1,plain,
% 1.84/1.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f24]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_27,plain,
% 1.84/1.02      ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_9,negated_conjecture,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_19,negated_conjecture,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.84/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_40,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK0,sK2,sK0),k1_enumset1(sK1,sK1,sK1)))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_21,c_19]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_42,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_27,c_40]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_289,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK1,sK0,sK2) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_229,c_42]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_498,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK0,sK2) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_417,c_289]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_43,plain,
% 1.84/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_27,c_28]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_499,plain,
% 1.84/1.02      ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK0,sK2) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_498,c_43]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_500,plain,
% 1.84/1.02      ( $false ),
% 1.84/1.02      inference(equality_resolution_simp,[status(thm)],[c_499]) ).
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  ------                               Statistics
% 1.84/1.02  
% 1.84/1.02  ------ General
% 1.84/1.02  
% 1.84/1.02  abstr_ref_over_cycles:                  0
% 1.84/1.02  abstr_ref_under_cycles:                 0
% 1.84/1.02  gc_basic_clause_elim:                   0
% 1.84/1.02  forced_gc_time:                         0
% 1.84/1.02  parsing_time:                           0.009
% 1.84/1.02  unif_index_cands_time:                  0.
% 1.84/1.02  unif_index_add_time:                    0.
% 1.84/1.02  orderings_time:                         0.
% 1.84/1.02  out_proof_time:                         0.013
% 1.84/1.02  total_time:                             0.075
% 1.84/1.02  num_of_symbols:                         39
% 1.84/1.02  num_of_terms:                           1373
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing
% 1.84/1.02  
% 1.84/1.02  num_of_splits:                          0
% 1.84/1.02  num_of_split_atoms:                     0
% 1.84/1.02  num_of_reused_defs:                     0
% 1.84/1.02  num_eq_ax_congr_red:                    3
% 1.84/1.02  num_of_sem_filtered_clauses:            0
% 1.84/1.02  num_of_subtypes:                        2
% 1.84/1.02  monotx_restored_types:                  0
% 1.84/1.02  sat_num_of_epr_types:                   0
% 1.84/1.02  sat_num_of_non_cyclic_types:            0
% 1.84/1.02  sat_guarded_non_collapsed_types:        0
% 1.84/1.02  num_pure_diseq_elim:                    0
% 1.84/1.02  simp_replaced_by:                       0
% 1.84/1.02  res_preprocessed:                       24
% 1.84/1.02  prep_upred:                             0
% 1.84/1.02  prep_unflattend:                        0
% 1.84/1.02  smt_new_axioms:                         0
% 1.84/1.02  pred_elim_cands:                        0
% 1.84/1.02  pred_elim:                              0
% 1.84/1.02  pred_elim_cl:                           0
% 1.84/1.02  pred_elim_cycles:                       0
% 1.84/1.02  merged_defs:                            0
% 1.84/1.02  merged_defs_ncl:                        0
% 1.84/1.02  bin_hyper_res:                          0
% 1.84/1.02  prep_cycles:                            2
% 1.84/1.02  pred_elim_time:                         0.
% 1.84/1.02  splitting_time:                         0.
% 1.84/1.02  sem_filter_time:                        0.
% 1.84/1.02  monotx_time:                            0.
% 1.84/1.02  subtype_inf_time:                       0.
% 1.84/1.02  
% 1.84/1.02  ------ Problem properties
% 1.84/1.02  
% 1.84/1.02  clauses:                                10
% 1.84/1.02  conjectures:                            1
% 1.84/1.02  epr:                                    0
% 1.84/1.02  horn:                                   10
% 1.84/1.02  ground:                                 1
% 1.84/1.02  unary:                                  10
% 1.84/1.02  binary:                                 0
% 1.84/1.02  lits:                                   10
% 1.84/1.02  lits_eq:                                10
% 1.84/1.02  fd_pure:                                0
% 1.84/1.02  fd_pseudo:                              0
% 1.84/1.02  fd_cond:                                0
% 1.84/1.02  fd_pseudo_cond:                         0
% 1.84/1.02  ac_symbols:                             0
% 1.84/1.02  
% 1.84/1.02  ------ Propositional Solver
% 1.84/1.02  
% 1.84/1.02  prop_solver_calls:                      13
% 1.84/1.02  prop_fast_solver_calls:                 60
% 1.84/1.02  smt_solver_calls:                       0
% 1.84/1.02  smt_fast_solver_calls:                  0
% 1.84/1.02  prop_num_of_clauses:                    48
% 1.84/1.02  prop_preprocess_simplified:             330
% 1.84/1.02  prop_fo_subsumed:                       0
% 1.84/1.02  prop_solver_time:                       0.
% 1.84/1.02  smt_solver_time:                        0.
% 1.84/1.02  smt_fast_solver_time:                   0.
% 1.84/1.02  prop_fast_solver_time:                  0.
% 1.84/1.02  prop_unsat_core_time:                   0.
% 1.84/1.02  
% 1.84/1.02  ------ QBF
% 1.84/1.02  
% 1.84/1.02  qbf_q_res:                              0
% 1.84/1.02  qbf_num_tautologies:                    0
% 1.84/1.02  qbf_prep_cycles:                        0
% 1.84/1.02  
% 1.84/1.02  ------ BMC1
% 1.84/1.02  
% 1.84/1.02  bmc1_current_bound:                     -1
% 1.84/1.02  bmc1_last_solved_bound:                 -1
% 1.84/1.02  bmc1_unsat_core_size:                   -1
% 1.84/1.02  bmc1_unsat_core_parents_size:           -1
% 1.84/1.02  bmc1_merge_next_fun:                    0
% 1.84/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation
% 1.84/1.02  
% 1.84/1.02  inst_num_of_clauses:                    0
% 1.84/1.02  inst_num_in_passive:                    0
% 1.84/1.02  inst_num_in_active:                     0
% 1.84/1.02  inst_num_in_unprocessed:                0
% 1.84/1.02  inst_num_of_loops:                      0
% 1.84/1.02  inst_num_of_learning_restarts:          0
% 1.84/1.02  inst_num_moves_active_passive:          0
% 1.84/1.02  inst_lit_activity:                      0
% 1.84/1.02  inst_lit_activity_moves:                0
% 1.84/1.02  inst_num_tautologies:                   0
% 1.84/1.02  inst_num_prop_implied:                  0
% 1.84/1.02  inst_num_existing_simplified:           0
% 1.84/1.02  inst_num_eq_res_simplified:             0
% 1.84/1.02  inst_num_child_elim:                    0
% 1.84/1.02  inst_num_of_dismatching_blockings:      0
% 1.84/1.02  inst_num_of_non_proper_insts:           0
% 1.84/1.02  inst_num_of_duplicates:                 0
% 1.84/1.02  inst_inst_num_from_inst_to_res:         0
% 1.84/1.02  inst_dismatching_checking_time:         0.
% 1.84/1.02  
% 1.84/1.02  ------ Resolution
% 1.84/1.02  
% 1.84/1.02  res_num_of_clauses:                     0
% 1.84/1.02  res_num_in_passive:                     0
% 1.84/1.02  res_num_in_active:                      0
% 1.84/1.02  res_num_of_loops:                       26
% 1.84/1.02  res_forward_subset_subsumed:            0
% 1.84/1.02  res_backward_subset_subsumed:           0
% 1.84/1.02  res_forward_subsumed:                   0
% 1.84/1.02  res_backward_subsumed:                  0
% 1.84/1.02  res_forward_subsumption_resolution:     0
% 1.84/1.02  res_backward_subsumption_resolution:    0
% 1.84/1.02  res_clause_to_clause_subsumption:       2045
% 1.84/1.02  res_orphan_elimination:                 0
% 1.84/1.02  res_tautology_del:                      0
% 1.84/1.02  res_num_eq_res_simplified:              0
% 1.84/1.02  res_num_sel_changes:                    0
% 1.84/1.02  res_moves_from_active_to_pass:          0
% 1.84/1.02  
% 1.84/1.02  ------ Superposition
% 1.84/1.02  
% 1.84/1.02  sup_time_total:                         0.
% 1.84/1.02  sup_time_generating:                    0.
% 1.84/1.02  sup_time_sim_full:                      0.
% 1.84/1.02  sup_time_sim_immed:                     0.
% 1.84/1.02  
% 1.84/1.02  sup_num_of_clauses:                     128
% 1.84/1.02  sup_num_in_active:                      17
% 1.84/1.02  sup_num_in_passive:                     111
% 1.84/1.02  sup_num_of_loops:                       20
% 1.84/1.02  sup_fw_superposition:                   163
% 1.84/1.02  sup_bw_superposition:                   267
% 1.84/1.02  sup_immediate_simplified:               33
% 1.84/1.02  sup_given_eliminated:                   0
% 1.84/1.02  comparisons_done:                       0
% 1.84/1.02  comparisons_avoided:                    0
% 1.84/1.02  
% 1.84/1.02  ------ Simplifications
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  sim_fw_subset_subsumed:                 0
% 1.84/1.02  sim_bw_subset_subsumed:                 0
% 1.84/1.02  sim_fw_subsumed:                        4
% 1.84/1.02  sim_bw_subsumed:                        6
% 1.84/1.02  sim_fw_subsumption_res:                 0
% 1.84/1.02  sim_bw_subsumption_res:                 0
% 1.84/1.02  sim_tautology_del:                      0
% 1.84/1.02  sim_eq_tautology_del:                   1
% 1.84/1.02  sim_eq_res_simp:                        0
% 1.84/1.02  sim_fw_demodulated:                     9
% 1.84/1.02  sim_bw_demodulated:                     5
% 1.84/1.02  sim_light_normalised:                   15
% 1.84/1.02  sim_joinable_taut:                      0
% 1.84/1.02  sim_joinable_simp:                      0
% 1.84/1.02  sim_ac_normalised:                      0
% 1.84/1.02  sim_smt_subsumption:                    0
% 1.84/1.02  
%------------------------------------------------------------------------------
