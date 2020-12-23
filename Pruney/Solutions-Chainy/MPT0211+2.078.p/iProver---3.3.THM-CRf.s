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
% DateTime   : Thu Dec  3 11:28:36 EST 2020

% Result     : Theorem 19.36s
% Output     : CNFRefutation 19.36s
% Verified   : 
% Statistics : Number of formulae       :   91 (1964 expanded)
%              Number of clauses        :   43 ( 289 expanded)
%              Number of leaves         :   17 ( 653 expanded)
%              Depth                    :   18
%              Number of atoms          :   92 (1965 expanded)
%              Number of equality atoms :   91 (1964 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f24,f39])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f29,f40,f40])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f28,f40,f40])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1))) ),
    inference(definition_unfolding,[],[f26,f40,f40])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))),k1_enumset1(X4,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))),k1_enumset1(X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f31,f24,f40,f34])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))),k1_enumset1(X3,X3,X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))),k1_enumset1(X3,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f36,f40,f43])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f25,f22,f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f27,f40,f40])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f38,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f38,f24,f34,f34])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)),k3_xboole_0(k1_enumset1(X3_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_138,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X2_35,X1_35,X0_35) ),
    inference(superposition,[status(thm)],[c_27,c_21])).

cnf(c_4450,plain,
    ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X1_35,X0_35,X0_35) ),
    inference(superposition,[status(thm)],[c_138,c_27])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)),k3_xboole_0(k1_enumset1(X3_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4505,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1_35,X2_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)),k3_xboole_0(k1_enumset1(X1_35,X2_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35))) ),
    inference(superposition,[status(thm)],[c_4450,c_22])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X3_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X3_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4515,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X2_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35))) ),
    inference(superposition,[status(thm)],[c_4450,c_24])).

cnf(c_4517,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X2_35,X1_35) ),
    inference(light_normalisation,[status(thm)],[c_4515,c_138])).

cnf(c_4519,plain,
    ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X2_35,X0_35) ),
    inference(demodulation,[status(thm)],[c_4505,c_4517])).

cnf(c_4555,plain,
    ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X2_35,X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_4519,c_4519])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35))),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35))),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_25,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) ),
    inference(demodulation,[status(thm)],[c_20,c_25,c_27])).

cnf(c_4499,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1_35,X0_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X1_35,X0_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35))) ),
    inference(superposition,[status(thm)],[c_4450,c_41])).

cnf(c_4521,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
    inference(demodulation,[status(thm)],[c_4499,c_4517])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_26,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_47,plain,
    ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(superposition,[status(thm)],[c_25,c_26])).

cnf(c_11535,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
    inference(superposition,[status(thm)],[c_4521,c_47])).

cnf(c_4420,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_138,c_22])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X0,X2),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X3,X0,X2),k1_enumset1(X1,X1,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X0_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X0_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4416,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X2_35,X1_35) ),
    inference(superposition,[status(thm)],[c_138,c_23])).

cnf(c_6518,plain,
    ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X0_35,X2_35,X1_35) ),
    inference(superposition,[status(thm)],[c_4420,c_4416])).

cnf(c_4556,plain,
    ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X0_35,X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_4519,c_4450])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_40,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_19,c_25])).

cnf(c_49,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_47,c_40])).

cnf(c_4522,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK0,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4519,c_49])).

cnf(c_4587,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK2,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK2,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_4519,c_4522])).

cnf(c_4589,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK2,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK2,sK2)))) != k1_enumset1(sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_4555,c_4587])).

cnf(c_4663,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_4556,c_4589])).

cnf(c_6648,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_6518,c_4663])).

cnf(c_30321,plain,
    ( k1_enumset1(sK0,sK2,sK1) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_11535,c_6648])).

cnf(c_30472,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4555,c_30321])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 19.36/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.36/3.00  
% 19.36/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.36/3.00  
% 19.36/3.00  ------  iProver source info
% 19.36/3.00  
% 19.36/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.36/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.36/3.00  git: non_committed_changes: false
% 19.36/3.00  git: last_make_outside_of_git: false
% 19.36/3.00  
% 19.36/3.00  ------ 
% 19.36/3.00  
% 19.36/3.00  ------ Input Options
% 19.36/3.00  
% 19.36/3.00  --out_options                           all
% 19.36/3.00  --tptp_safe_out                         true
% 19.36/3.00  --problem_path                          ""
% 19.36/3.00  --include_path                          ""
% 19.36/3.00  --clausifier                            res/vclausify_rel
% 19.36/3.00  --clausifier_options                    --mode clausify
% 19.36/3.00  --stdin                                 false
% 19.36/3.00  --stats_out                             all
% 19.36/3.00  
% 19.36/3.00  ------ General Options
% 19.36/3.00  
% 19.36/3.00  --fof                                   false
% 19.36/3.00  --time_out_real                         305.
% 19.36/3.00  --time_out_virtual                      -1.
% 19.36/3.00  --symbol_type_check                     false
% 19.36/3.00  --clausify_out                          false
% 19.36/3.00  --sig_cnt_out                           false
% 19.36/3.00  --trig_cnt_out                          false
% 19.36/3.00  --trig_cnt_out_tolerance                1.
% 19.36/3.00  --trig_cnt_out_sk_spl                   false
% 19.36/3.00  --abstr_cl_out                          false
% 19.36/3.00  
% 19.36/3.00  ------ Global Options
% 19.36/3.00  
% 19.36/3.00  --schedule                              default
% 19.36/3.00  --add_important_lit                     false
% 19.36/3.00  --prop_solver_per_cl                    1000
% 19.36/3.00  --min_unsat_core                        false
% 19.36/3.00  --soft_assumptions                      false
% 19.36/3.00  --soft_lemma_size                       3
% 19.36/3.00  --prop_impl_unit_size                   0
% 19.36/3.00  --prop_impl_unit                        []
% 19.36/3.00  --share_sel_clauses                     true
% 19.36/3.00  --reset_solvers                         false
% 19.36/3.00  --bc_imp_inh                            [conj_cone]
% 19.36/3.00  --conj_cone_tolerance                   3.
% 19.36/3.00  --extra_neg_conj                        none
% 19.36/3.00  --large_theory_mode                     true
% 19.36/3.00  --prolific_symb_bound                   200
% 19.36/3.00  --lt_threshold                          2000
% 19.36/3.00  --clause_weak_htbl                      true
% 19.36/3.00  --gc_record_bc_elim                     false
% 19.36/3.00  
% 19.36/3.00  ------ Preprocessing Options
% 19.36/3.00  
% 19.36/3.00  --preprocessing_flag                    true
% 19.36/3.00  --time_out_prep_mult                    0.1
% 19.36/3.00  --splitting_mode                        input
% 19.36/3.00  --splitting_grd                         true
% 19.36/3.00  --splitting_cvd                         false
% 19.36/3.00  --splitting_cvd_svl                     false
% 19.36/3.00  --splitting_nvd                         32
% 19.36/3.00  --sub_typing                            true
% 19.36/3.00  --prep_gs_sim                           true
% 19.36/3.00  --prep_unflatten                        true
% 19.36/3.00  --prep_res_sim                          true
% 19.36/3.00  --prep_upred                            true
% 19.36/3.00  --prep_sem_filter                       exhaustive
% 19.36/3.00  --prep_sem_filter_out                   false
% 19.36/3.00  --pred_elim                             true
% 19.36/3.00  --res_sim_input                         true
% 19.36/3.00  --eq_ax_congr_red                       true
% 19.36/3.00  --pure_diseq_elim                       true
% 19.36/3.00  --brand_transform                       false
% 19.36/3.00  --non_eq_to_eq                          false
% 19.36/3.00  --prep_def_merge                        true
% 19.36/3.00  --prep_def_merge_prop_impl              false
% 19.36/3.00  --prep_def_merge_mbd                    true
% 19.36/3.00  --prep_def_merge_tr_red                 false
% 19.36/3.00  --prep_def_merge_tr_cl                  false
% 19.36/3.00  --smt_preprocessing                     true
% 19.36/3.00  --smt_ac_axioms                         fast
% 19.36/3.00  --preprocessed_out                      false
% 19.36/3.00  --preprocessed_stats                    false
% 19.36/3.00  
% 19.36/3.00  ------ Abstraction refinement Options
% 19.36/3.00  
% 19.36/3.00  --abstr_ref                             []
% 19.36/3.00  --abstr_ref_prep                        false
% 19.36/3.00  --abstr_ref_until_sat                   false
% 19.36/3.00  --abstr_ref_sig_restrict                funpre
% 19.36/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.36/3.00  --abstr_ref_under                       []
% 19.36/3.00  
% 19.36/3.00  ------ SAT Options
% 19.36/3.00  
% 19.36/3.00  --sat_mode                              false
% 19.36/3.00  --sat_fm_restart_options                ""
% 19.36/3.00  --sat_gr_def                            false
% 19.36/3.00  --sat_epr_types                         true
% 19.36/3.00  --sat_non_cyclic_types                  false
% 19.36/3.00  --sat_finite_models                     false
% 19.36/3.00  --sat_fm_lemmas                         false
% 19.36/3.00  --sat_fm_prep                           false
% 19.36/3.00  --sat_fm_uc_incr                        true
% 19.36/3.00  --sat_out_model                         small
% 19.36/3.00  --sat_out_clauses                       false
% 19.36/3.00  
% 19.36/3.00  ------ QBF Options
% 19.36/3.00  
% 19.36/3.00  --qbf_mode                              false
% 19.36/3.00  --qbf_elim_univ                         false
% 19.36/3.00  --qbf_dom_inst                          none
% 19.36/3.00  --qbf_dom_pre_inst                      false
% 19.36/3.00  --qbf_sk_in                             false
% 19.36/3.00  --qbf_pred_elim                         true
% 19.36/3.00  --qbf_split                             512
% 19.36/3.00  
% 19.36/3.00  ------ BMC1 Options
% 19.36/3.00  
% 19.36/3.00  --bmc1_incremental                      false
% 19.36/3.00  --bmc1_axioms                           reachable_all
% 19.36/3.00  --bmc1_min_bound                        0
% 19.36/3.00  --bmc1_max_bound                        -1
% 19.36/3.00  --bmc1_max_bound_default                -1
% 19.36/3.00  --bmc1_symbol_reachability              true
% 19.36/3.00  --bmc1_property_lemmas                  false
% 19.36/3.00  --bmc1_k_induction                      false
% 19.36/3.00  --bmc1_non_equiv_states                 false
% 19.36/3.00  --bmc1_deadlock                         false
% 19.36/3.00  --bmc1_ucm                              false
% 19.36/3.00  --bmc1_add_unsat_core                   none
% 19.36/3.00  --bmc1_unsat_core_children              false
% 19.36/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.36/3.00  --bmc1_out_stat                         full
% 19.36/3.00  --bmc1_ground_init                      false
% 19.36/3.00  --bmc1_pre_inst_next_state              false
% 19.36/3.00  --bmc1_pre_inst_state                   false
% 19.36/3.00  --bmc1_pre_inst_reach_state             false
% 19.36/3.00  --bmc1_out_unsat_core                   false
% 19.36/3.00  --bmc1_aig_witness_out                  false
% 19.36/3.00  --bmc1_verbose                          false
% 19.36/3.00  --bmc1_dump_clauses_tptp                false
% 19.36/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.36/3.00  --bmc1_dump_file                        -
% 19.36/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.36/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.36/3.00  --bmc1_ucm_extend_mode                  1
% 19.36/3.00  --bmc1_ucm_init_mode                    2
% 19.36/3.00  --bmc1_ucm_cone_mode                    none
% 19.36/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.36/3.00  --bmc1_ucm_relax_model                  4
% 19.36/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.36/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.36/3.00  --bmc1_ucm_layered_model                none
% 19.36/3.00  --bmc1_ucm_max_lemma_size               10
% 19.36/3.00  
% 19.36/3.00  ------ AIG Options
% 19.36/3.00  
% 19.36/3.00  --aig_mode                              false
% 19.36/3.00  
% 19.36/3.00  ------ Instantiation Options
% 19.36/3.00  
% 19.36/3.00  --instantiation_flag                    true
% 19.36/3.00  --inst_sos_flag                         false
% 19.36/3.00  --inst_sos_phase                        true
% 19.36/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.36/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.36/3.00  --inst_lit_sel_side                     num_symb
% 19.36/3.00  --inst_solver_per_active                1400
% 19.36/3.00  --inst_solver_calls_frac                1.
% 19.36/3.00  --inst_passive_queue_type               priority_queues
% 19.36/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.36/3.00  --inst_passive_queues_freq              [25;2]
% 19.36/3.00  --inst_dismatching                      true
% 19.36/3.00  --inst_eager_unprocessed_to_passive     true
% 19.36/3.00  --inst_prop_sim_given                   true
% 19.36/3.00  --inst_prop_sim_new                     false
% 19.36/3.00  --inst_subs_new                         false
% 19.36/3.00  --inst_eq_res_simp                      false
% 19.36/3.00  --inst_subs_given                       false
% 19.36/3.00  --inst_orphan_elimination               true
% 19.36/3.00  --inst_learning_loop_flag               true
% 19.36/3.00  --inst_learning_start                   3000
% 19.36/3.00  --inst_learning_factor                  2
% 19.36/3.00  --inst_start_prop_sim_after_learn       3
% 19.36/3.00  --inst_sel_renew                        solver
% 19.36/3.00  --inst_lit_activity_flag                true
% 19.36/3.00  --inst_restr_to_given                   false
% 19.36/3.00  --inst_activity_threshold               500
% 19.36/3.00  --inst_out_proof                        true
% 19.36/3.00  
% 19.36/3.00  ------ Resolution Options
% 19.36/3.00  
% 19.36/3.00  --resolution_flag                       true
% 19.36/3.00  --res_lit_sel                           adaptive
% 19.36/3.00  --res_lit_sel_side                      none
% 19.36/3.00  --res_ordering                          kbo
% 19.36/3.00  --res_to_prop_solver                    active
% 19.36/3.00  --res_prop_simpl_new                    false
% 19.36/3.00  --res_prop_simpl_given                  true
% 19.36/3.00  --res_passive_queue_type                priority_queues
% 19.36/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.36/3.00  --res_passive_queues_freq               [15;5]
% 19.36/3.00  --res_forward_subs                      full
% 19.36/3.00  --res_backward_subs                     full
% 19.36/3.00  --res_forward_subs_resolution           true
% 19.36/3.00  --res_backward_subs_resolution          true
% 19.36/3.00  --res_orphan_elimination                true
% 19.36/3.00  --res_time_limit                        2.
% 19.36/3.00  --res_out_proof                         true
% 19.36/3.00  
% 19.36/3.00  ------ Superposition Options
% 19.36/3.00  
% 19.36/3.00  --superposition_flag                    true
% 19.36/3.00  --sup_passive_queue_type                priority_queues
% 19.36/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.36/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.36/3.00  --demod_completeness_check              fast
% 19.36/3.00  --demod_use_ground                      true
% 19.36/3.00  --sup_to_prop_solver                    passive
% 19.36/3.00  --sup_prop_simpl_new                    true
% 19.36/3.00  --sup_prop_simpl_given                  true
% 19.36/3.00  --sup_fun_splitting                     false
% 19.36/3.00  --sup_smt_interval                      50000
% 19.36/3.00  
% 19.36/3.00  ------ Superposition Simplification Setup
% 19.36/3.00  
% 19.36/3.00  --sup_indices_passive                   []
% 19.36/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.36/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.36/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.36/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.36/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.36/3.00  --sup_full_bw                           [BwDemod]
% 19.36/3.00  --sup_immed_triv                        [TrivRules]
% 19.36/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.36/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.36/3.00  --sup_immed_bw_main                     []
% 19.36/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.36/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.36/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.36/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.36/3.00  
% 19.36/3.00  ------ Combination Options
% 19.36/3.00  
% 19.36/3.00  --comb_res_mult                         3
% 19.36/3.00  --comb_sup_mult                         2
% 19.36/3.00  --comb_inst_mult                        10
% 19.36/3.00  
% 19.36/3.00  ------ Debug Options
% 19.36/3.00  
% 19.36/3.00  --dbg_backtrace                         false
% 19.36/3.00  --dbg_dump_prop_clauses                 false
% 19.36/3.00  --dbg_dump_prop_clauses_file            -
% 19.36/3.00  --dbg_out_stat                          false
% 19.36/3.00  ------ Parsing...
% 19.36/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.36/3.00  
% 19.36/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 19.36/3.00  
% 19.36/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.36/3.00  
% 19.36/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.36/3.00  ------ Proving...
% 19.36/3.00  ------ Problem Properties 
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  clauses                                 9
% 19.36/3.00  conjectures                             1
% 19.36/3.00  EPR                                     0
% 19.36/3.00  Horn                                    9
% 19.36/3.00  unary                                   9
% 19.36/3.00  binary                                  0
% 19.36/3.00  lits                                    9
% 19.36/3.00  lits eq                                 9
% 19.36/3.00  fd_pure                                 0
% 19.36/3.00  fd_pseudo                               0
% 19.36/3.00  fd_cond                                 0
% 19.36/3.00  fd_pseudo_cond                          0
% 19.36/3.00  AC symbols                              0
% 19.36/3.00  
% 19.36/3.00  ------ Schedule UEQ
% 19.36/3.00  
% 19.36/3.00  ------ pure equality problem: resolution off 
% 19.36/3.00  
% 19.36/3.00  ------ Option_UEQ Time Limit: Unbounded
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  ------ 
% 19.36/3.00  Current options:
% 19.36/3.00  ------ 
% 19.36/3.00  
% 19.36/3.00  ------ Input Options
% 19.36/3.00  
% 19.36/3.00  --out_options                           all
% 19.36/3.00  --tptp_safe_out                         true
% 19.36/3.00  --problem_path                          ""
% 19.36/3.00  --include_path                          ""
% 19.36/3.00  --clausifier                            res/vclausify_rel
% 19.36/3.00  --clausifier_options                    --mode clausify
% 19.36/3.00  --stdin                                 false
% 19.36/3.00  --stats_out                             all
% 19.36/3.00  
% 19.36/3.00  ------ General Options
% 19.36/3.00  
% 19.36/3.00  --fof                                   false
% 19.36/3.00  --time_out_real                         305.
% 19.36/3.00  --time_out_virtual                      -1.
% 19.36/3.00  --symbol_type_check                     false
% 19.36/3.00  --clausify_out                          false
% 19.36/3.00  --sig_cnt_out                           false
% 19.36/3.00  --trig_cnt_out                          false
% 19.36/3.00  --trig_cnt_out_tolerance                1.
% 19.36/3.00  --trig_cnt_out_sk_spl                   false
% 19.36/3.00  --abstr_cl_out                          false
% 19.36/3.00  
% 19.36/3.00  ------ Global Options
% 19.36/3.00  
% 19.36/3.00  --schedule                              default
% 19.36/3.00  --add_important_lit                     false
% 19.36/3.00  --prop_solver_per_cl                    1000
% 19.36/3.00  --min_unsat_core                        false
% 19.36/3.00  --soft_assumptions                      false
% 19.36/3.00  --soft_lemma_size                       3
% 19.36/3.00  --prop_impl_unit_size                   0
% 19.36/3.00  --prop_impl_unit                        []
% 19.36/3.00  --share_sel_clauses                     true
% 19.36/3.00  --reset_solvers                         false
% 19.36/3.00  --bc_imp_inh                            [conj_cone]
% 19.36/3.00  --conj_cone_tolerance                   3.
% 19.36/3.00  --extra_neg_conj                        none
% 19.36/3.00  --large_theory_mode                     true
% 19.36/3.00  --prolific_symb_bound                   200
% 19.36/3.00  --lt_threshold                          2000
% 19.36/3.00  --clause_weak_htbl                      true
% 19.36/3.00  --gc_record_bc_elim                     false
% 19.36/3.00  
% 19.36/3.00  ------ Preprocessing Options
% 19.36/3.00  
% 19.36/3.00  --preprocessing_flag                    true
% 19.36/3.00  --time_out_prep_mult                    0.1
% 19.36/3.00  --splitting_mode                        input
% 19.36/3.00  --splitting_grd                         true
% 19.36/3.00  --splitting_cvd                         false
% 19.36/3.00  --splitting_cvd_svl                     false
% 19.36/3.00  --splitting_nvd                         32
% 19.36/3.00  --sub_typing                            true
% 19.36/3.00  --prep_gs_sim                           true
% 19.36/3.00  --prep_unflatten                        true
% 19.36/3.00  --prep_res_sim                          true
% 19.36/3.00  --prep_upred                            true
% 19.36/3.00  --prep_sem_filter                       exhaustive
% 19.36/3.00  --prep_sem_filter_out                   false
% 19.36/3.00  --pred_elim                             true
% 19.36/3.00  --res_sim_input                         true
% 19.36/3.00  --eq_ax_congr_red                       true
% 19.36/3.00  --pure_diseq_elim                       true
% 19.36/3.00  --brand_transform                       false
% 19.36/3.00  --non_eq_to_eq                          false
% 19.36/3.00  --prep_def_merge                        true
% 19.36/3.00  --prep_def_merge_prop_impl              false
% 19.36/3.00  --prep_def_merge_mbd                    true
% 19.36/3.00  --prep_def_merge_tr_red                 false
% 19.36/3.00  --prep_def_merge_tr_cl                  false
% 19.36/3.00  --smt_preprocessing                     true
% 19.36/3.00  --smt_ac_axioms                         fast
% 19.36/3.00  --preprocessed_out                      false
% 19.36/3.00  --preprocessed_stats                    false
% 19.36/3.00  
% 19.36/3.00  ------ Abstraction refinement Options
% 19.36/3.00  
% 19.36/3.00  --abstr_ref                             []
% 19.36/3.00  --abstr_ref_prep                        false
% 19.36/3.00  --abstr_ref_until_sat                   false
% 19.36/3.00  --abstr_ref_sig_restrict                funpre
% 19.36/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.36/3.00  --abstr_ref_under                       []
% 19.36/3.00  
% 19.36/3.00  ------ SAT Options
% 19.36/3.00  
% 19.36/3.00  --sat_mode                              false
% 19.36/3.00  --sat_fm_restart_options                ""
% 19.36/3.00  --sat_gr_def                            false
% 19.36/3.00  --sat_epr_types                         true
% 19.36/3.00  --sat_non_cyclic_types                  false
% 19.36/3.00  --sat_finite_models                     false
% 19.36/3.00  --sat_fm_lemmas                         false
% 19.36/3.00  --sat_fm_prep                           false
% 19.36/3.00  --sat_fm_uc_incr                        true
% 19.36/3.00  --sat_out_model                         small
% 19.36/3.00  --sat_out_clauses                       false
% 19.36/3.00  
% 19.36/3.00  ------ QBF Options
% 19.36/3.00  
% 19.36/3.00  --qbf_mode                              false
% 19.36/3.00  --qbf_elim_univ                         false
% 19.36/3.00  --qbf_dom_inst                          none
% 19.36/3.00  --qbf_dom_pre_inst                      false
% 19.36/3.00  --qbf_sk_in                             false
% 19.36/3.00  --qbf_pred_elim                         true
% 19.36/3.00  --qbf_split                             512
% 19.36/3.00  
% 19.36/3.00  ------ BMC1 Options
% 19.36/3.00  
% 19.36/3.00  --bmc1_incremental                      false
% 19.36/3.00  --bmc1_axioms                           reachable_all
% 19.36/3.00  --bmc1_min_bound                        0
% 19.36/3.00  --bmc1_max_bound                        -1
% 19.36/3.00  --bmc1_max_bound_default                -1
% 19.36/3.00  --bmc1_symbol_reachability              true
% 19.36/3.00  --bmc1_property_lemmas                  false
% 19.36/3.00  --bmc1_k_induction                      false
% 19.36/3.00  --bmc1_non_equiv_states                 false
% 19.36/3.00  --bmc1_deadlock                         false
% 19.36/3.00  --bmc1_ucm                              false
% 19.36/3.00  --bmc1_add_unsat_core                   none
% 19.36/3.00  --bmc1_unsat_core_children              false
% 19.36/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.36/3.00  --bmc1_out_stat                         full
% 19.36/3.00  --bmc1_ground_init                      false
% 19.36/3.00  --bmc1_pre_inst_next_state              false
% 19.36/3.00  --bmc1_pre_inst_state                   false
% 19.36/3.00  --bmc1_pre_inst_reach_state             false
% 19.36/3.00  --bmc1_out_unsat_core                   false
% 19.36/3.00  --bmc1_aig_witness_out                  false
% 19.36/3.00  --bmc1_verbose                          false
% 19.36/3.00  --bmc1_dump_clauses_tptp                false
% 19.36/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.36/3.00  --bmc1_dump_file                        -
% 19.36/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.36/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.36/3.00  --bmc1_ucm_extend_mode                  1
% 19.36/3.00  --bmc1_ucm_init_mode                    2
% 19.36/3.00  --bmc1_ucm_cone_mode                    none
% 19.36/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.36/3.00  --bmc1_ucm_relax_model                  4
% 19.36/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.36/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.36/3.00  --bmc1_ucm_layered_model                none
% 19.36/3.00  --bmc1_ucm_max_lemma_size               10
% 19.36/3.00  
% 19.36/3.00  ------ AIG Options
% 19.36/3.00  
% 19.36/3.00  --aig_mode                              false
% 19.36/3.00  
% 19.36/3.00  ------ Instantiation Options
% 19.36/3.00  
% 19.36/3.00  --instantiation_flag                    false
% 19.36/3.00  --inst_sos_flag                         false
% 19.36/3.00  --inst_sos_phase                        true
% 19.36/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.36/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.36/3.00  --inst_lit_sel_side                     num_symb
% 19.36/3.00  --inst_solver_per_active                1400
% 19.36/3.00  --inst_solver_calls_frac                1.
% 19.36/3.00  --inst_passive_queue_type               priority_queues
% 19.36/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.36/3.00  --inst_passive_queues_freq              [25;2]
% 19.36/3.00  --inst_dismatching                      true
% 19.36/3.00  --inst_eager_unprocessed_to_passive     true
% 19.36/3.00  --inst_prop_sim_given                   true
% 19.36/3.00  --inst_prop_sim_new                     false
% 19.36/3.00  --inst_subs_new                         false
% 19.36/3.00  --inst_eq_res_simp                      false
% 19.36/3.00  --inst_subs_given                       false
% 19.36/3.00  --inst_orphan_elimination               true
% 19.36/3.00  --inst_learning_loop_flag               true
% 19.36/3.00  --inst_learning_start                   3000
% 19.36/3.00  --inst_learning_factor                  2
% 19.36/3.00  --inst_start_prop_sim_after_learn       3
% 19.36/3.00  --inst_sel_renew                        solver
% 19.36/3.00  --inst_lit_activity_flag                true
% 19.36/3.00  --inst_restr_to_given                   false
% 19.36/3.00  --inst_activity_threshold               500
% 19.36/3.00  --inst_out_proof                        true
% 19.36/3.00  
% 19.36/3.00  ------ Resolution Options
% 19.36/3.00  
% 19.36/3.00  --resolution_flag                       false
% 19.36/3.00  --res_lit_sel                           adaptive
% 19.36/3.00  --res_lit_sel_side                      none
% 19.36/3.00  --res_ordering                          kbo
% 19.36/3.00  --res_to_prop_solver                    active
% 19.36/3.00  --res_prop_simpl_new                    false
% 19.36/3.00  --res_prop_simpl_given                  true
% 19.36/3.00  --res_passive_queue_type                priority_queues
% 19.36/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.36/3.00  --res_passive_queues_freq               [15;5]
% 19.36/3.00  --res_forward_subs                      full
% 19.36/3.00  --res_backward_subs                     full
% 19.36/3.00  --res_forward_subs_resolution           true
% 19.36/3.00  --res_backward_subs_resolution          true
% 19.36/3.00  --res_orphan_elimination                true
% 19.36/3.00  --res_time_limit                        2.
% 19.36/3.00  --res_out_proof                         true
% 19.36/3.00  
% 19.36/3.00  ------ Superposition Options
% 19.36/3.00  
% 19.36/3.00  --superposition_flag                    true
% 19.36/3.00  --sup_passive_queue_type                priority_queues
% 19.36/3.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.36/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.36/3.00  --demod_completeness_check              fast
% 19.36/3.00  --demod_use_ground                      true
% 19.36/3.00  --sup_to_prop_solver                    active
% 19.36/3.00  --sup_prop_simpl_new                    false
% 19.36/3.00  --sup_prop_simpl_given                  false
% 19.36/3.00  --sup_fun_splitting                     true
% 19.36/3.00  --sup_smt_interval                      10000
% 19.36/3.00  
% 19.36/3.00  ------ Superposition Simplification Setup
% 19.36/3.00  
% 19.36/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.36/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.36/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.36/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.36/3.00  --sup_full_triv                         [TrivRules]
% 19.36/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.36/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.36/3.00  --sup_immed_triv                        [TrivRules]
% 19.36/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.36/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.36/3.00  --sup_immed_bw_main                     []
% 19.36/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.36/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.36/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.36/3.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 19.36/3.00  
% 19.36/3.00  ------ Combination Options
% 19.36/3.00  
% 19.36/3.00  --comb_res_mult                         1
% 19.36/3.00  --comb_sup_mult                         1
% 19.36/3.00  --comb_inst_mult                        1000000
% 19.36/3.00  
% 19.36/3.00  ------ Debug Options
% 19.36/3.00  
% 19.36/3.00  --dbg_backtrace                         false
% 19.36/3.00  --dbg_dump_prop_clauses                 false
% 19.36/3.00  --dbg_dump_prop_clauses_file            -
% 19.36/3.00  --dbg_out_stat                          false
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  ------ Proving...
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  % SZS status Theorem for theBenchmark.p
% 19.36/3.00  
% 19.36/3.00   Resolution empty clause
% 19.36/3.00  
% 19.36/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.36/3.00  
% 19.36/3.00  fof(f14,axiom,(
% 19.36/3.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f35,plain,(
% 19.36/3.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f14])).
% 19.36/3.00  
% 19.36/3.00  fof(f9,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f30,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f9])).
% 19.36/3.00  
% 19.36/3.00  fof(f3,axiom,(
% 19.36/3.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f24,plain,(
% 19.36/3.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f3])).
% 19.36/3.00  
% 19.36/3.00  fof(f12,axiom,(
% 19.36/3.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f33,plain,(
% 19.36/3.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f12])).
% 19.36/3.00  
% 19.36/3.00  fof(f13,axiom,(
% 19.36/3.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f34,plain,(
% 19.36/3.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f13])).
% 19.36/3.00  
% 19.36/3.00  fof(f39,plain,(
% 19.36/3.00    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 19.36/3.00    inference(definition_unfolding,[],[f33,f34])).
% 19.36/3.00  
% 19.36/3.00  fof(f40,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 19.36/3.00    inference(definition_unfolding,[],[f30,f24,f39])).
% 19.36/3.00  
% 19.36/3.00  fof(f44,plain,(
% 19.36/3.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2)) )),
% 19.36/3.00    inference(definition_unfolding,[],[f35,f40])).
% 19.36/3.00  
% 19.36/3.00  fof(f8,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f29,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f8])).
% 19.36/3.00  
% 19.36/3.00  fof(f49,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0)))) )),
% 19.36/3.00    inference(definition_unfolding,[],[f29,f40,f40])).
% 19.36/3.00  
% 19.36/3.00  fof(f7,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f28,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f7])).
% 19.36/3.00  
% 19.36/3.00  fof(f48,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0)))) )),
% 19.36/3.00    inference(definition_unfolding,[],[f28,f40,f40])).
% 19.36/3.00  
% 19.36/3.00  fof(f5,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f26,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f5])).
% 19.36/3.00  
% 19.36/3.00  fof(f46,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1)))) )),
% 19.36/3.00    inference(definition_unfolding,[],[f26,f40,f40])).
% 19.36/3.00  
% 19.36/3.00  fof(f15,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f36,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f15])).
% 19.36/3.00  
% 19.36/3.00  fof(f16,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f37,plain,(
% 19.36/3.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f16])).
% 19.36/3.00  
% 19.36/3.00  fof(f10,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f31,plain,(
% 19.36/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f10])).
% 19.36/3.00  
% 19.36/3.00  fof(f41,plain,(
% 19.36/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))),k1_enumset1(X4,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))),k1_enumset1(X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 19.36/3.00    inference(definition_unfolding,[],[f31,f24,f40,f34])).
% 19.36/3.00  
% 19.36/3.00  fof(f43,plain,(
% 19.36/3.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))),k1_enumset1(X3,X3,X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))),k1_enumset1(X3,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 19.36/3.00    inference(definition_unfolding,[],[f37,f41])).
% 19.36/3.00  
% 19.36/3.00  fof(f50,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)))) )),
% 19.36/3.00    inference(definition_unfolding,[],[f36,f40,f43])).
% 19.36/3.00  
% 19.36/3.00  fof(f4,axiom,(
% 19.36/3.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f25,plain,(
% 19.36/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f4])).
% 19.36/3.00  
% 19.36/3.00  fof(f1,axiom,(
% 19.36/3.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f22,plain,(
% 19.36/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.36/3.00    inference(cnf_transformation,[],[f1])).
% 19.36/3.00  
% 19.36/3.00  fof(f45,plain,(
% 19.36/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 19.36/3.00    inference(definition_unfolding,[],[f25,f22,f24])).
% 19.36/3.00  
% 19.36/3.00  fof(f2,axiom,(
% 19.36/3.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f23,plain,(
% 19.36/3.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f2])).
% 19.36/3.00  
% 19.36/3.00  fof(f6,axiom,(
% 19.36/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f27,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 19.36/3.00    inference(cnf_transformation,[],[f6])).
% 19.36/3.00  
% 19.36/3.00  fof(f47,plain,(
% 19.36/3.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0)))) )),
% 19.36/3.00    inference(definition_unfolding,[],[f27,f40,f40])).
% 19.36/3.00  
% 19.36/3.00  fof(f17,conjecture,(
% 19.36/3.00    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 19.36/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.36/3.00  
% 19.36/3.00  fof(f18,negated_conjecture,(
% 19.36/3.00    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 19.36/3.00    inference(negated_conjecture,[],[f17])).
% 19.36/3.00  
% 19.36/3.00  fof(f19,plain,(
% 19.36/3.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 19.36/3.00    inference(ennf_transformation,[],[f18])).
% 19.36/3.00  
% 19.36/3.00  fof(f20,plain,(
% 19.36/3.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 19.36/3.00    introduced(choice_axiom,[])).
% 19.36/3.00  
% 19.36/3.00  fof(f21,plain,(
% 19.36/3.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 19.36/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 19.36/3.00  
% 19.36/3.00  fof(f38,plain,(
% 19.36/3.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 19.36/3.00    inference(cnf_transformation,[],[f21])).
% 19.36/3.00  
% 19.36/3.00  fof(f51,plain,(
% 19.36/3.00    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 19.36/3.00    inference(definition_unfolding,[],[f38,f24,f34,f34])).
% 19.36/3.00  
% 19.36/3.00  cnf(c_0,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
% 19.36/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_27,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_0]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_6,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0))) ),
% 19.36/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_21,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)),k3_xboole_0(k1_enumset1(X3_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35))) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_6]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_138,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X2_35,X1_35,X0_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_27,c_21]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4450,plain,
% 19.36/3.00      ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X1_35,X0_35,X0_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_138,c_27]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_5,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0)),k3_xboole_0(k1_enumset1(X3,X1,X2),k1_enumset1(X0,X0,X0))) ),
% 19.36/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_22,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)),k3_xboole_0(k1_enumset1(X3_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35))) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_5]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4505,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1_35,X2_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)),k3_xboole_0(k1_enumset1(X1_35,X2_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35))) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4450,c_22]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_3,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X3,X2),k1_enumset1(X1,X1,X1))) ),
% 19.36/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_24,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X3_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X3_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35))) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_3]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4515,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X2_35,X2_35,X2_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X2_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35))) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4450,c_24]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4517,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X2_35,X1_35) ),
% 19.36/3.00      inference(light_normalisation,[status(thm)],[c_4515,c_138]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4519,plain,
% 19.36/3.00      ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X2_35,X0_35) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_4505,c_4517]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4555,plain,
% 19.36/3.00      ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X2_35,X0_35,X1_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4519,c_4519]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_7,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
% 19.36/3.00      inference(cnf_transformation,[],[f50]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_20,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35))),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X1_35))),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_7]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_2,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 19.36/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_25,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_2]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_41,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_20,c_25,c_27]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4499,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1_35,X0_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X1_35,X0_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35))) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4450,c_41]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4521,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_4499,c_4517]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_1,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.36/3.00      inference(cnf_transformation,[],[f23]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_26,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_1]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_47,plain,
% 19.36/3.00      ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_25,c_26]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_11535,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4521,c_47]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4420,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_138,c_22]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X0,X2),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X3,X0,X2),k1_enumset1(X1,X1,X1))) ),
% 19.36/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_23,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k1_enumset1(X3_35,X3_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X0_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X0_35,X2_35),k1_enumset1(X1_35,X1_35,X1_35))) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_4]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4416,plain,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35))) = k1_enumset1(X0_35,X2_35,X1_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_138,c_23]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_6518,plain,
% 19.36/3.00      ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X0_35,X2_35,X1_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4420,c_4416]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4556,plain,
% 19.36/3.00      ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X0_35,X0_35,X1_35) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4519,c_4450]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_8,negated_conjecture,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 19.36/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_19,negated_conjecture,
% 19.36/3.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 19.36/3.00      inference(subtyping,[status(esa)],[c_8]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_40,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_19,c_25]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_49,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_47,c_40]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4522,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK0,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_4519,c_49]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4587,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK2,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK2,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4519,c_4522]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4589,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK2,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK2,sK2)))) != k1_enumset1(sK1,sK2,sK0) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_4555,c_4587]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_4663,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK2,sK0) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_4556,c_4589]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_6648,plain,
% 19.36/3.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK0,sK2) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_6518,c_4663]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_30321,plain,
% 19.36/3.00      ( k1_enumset1(sK0,sK2,sK1) != k1_enumset1(sK1,sK0,sK2) ),
% 19.36/3.00      inference(demodulation,[status(thm)],[c_11535,c_6648]) ).
% 19.36/3.00  
% 19.36/3.00  cnf(c_30472,plain,
% 19.36/3.00      ( $false ),
% 19.36/3.00      inference(superposition,[status(thm)],[c_4555,c_30321]) ).
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.36/3.00  
% 19.36/3.00  ------                               Statistics
% 19.36/3.00  
% 19.36/3.00  ------ General
% 19.36/3.00  
% 19.36/3.00  abstr_ref_over_cycles:                  0
% 19.36/3.00  abstr_ref_under_cycles:                 0
% 19.36/3.00  gc_basic_clause_elim:                   0
% 19.36/3.00  forced_gc_time:                         0
% 19.36/3.00  parsing_time:                           0.01
% 19.36/3.00  unif_index_cands_time:                  0.
% 19.36/3.00  unif_index_add_time:                    0.
% 19.36/3.00  orderings_time:                         0.
% 19.36/3.00  out_proof_time:                         0.009
% 19.36/3.00  total_time:                             2.025
% 19.36/3.00  num_of_symbols:                         39
% 19.36/3.00  num_of_terms:                           82345
% 19.36/3.00  
% 19.36/3.00  ------ Preprocessing
% 19.36/3.00  
% 19.36/3.00  num_of_splits:                          0
% 19.36/3.00  num_of_split_atoms:                     0
% 19.36/3.00  num_of_reused_defs:                     0
% 19.36/3.00  num_eq_ax_congr_red:                    3
% 19.36/3.00  num_of_sem_filtered_clauses:            0
% 19.36/3.00  num_of_subtypes:                        2
% 19.36/3.00  monotx_restored_types:                  0
% 19.36/3.00  sat_num_of_epr_types:                   0
% 19.36/3.00  sat_num_of_non_cyclic_types:            0
% 19.36/3.00  sat_guarded_non_collapsed_types:        0
% 19.36/3.00  num_pure_diseq_elim:                    0
% 19.36/3.00  simp_replaced_by:                       0
% 19.36/3.00  res_preprocessed:                       22
% 19.36/3.00  prep_upred:                             0
% 19.36/3.00  prep_unflattend:                        0
% 19.36/3.00  smt_new_axioms:                         0
% 19.36/3.00  pred_elim_cands:                        0
% 19.36/3.00  pred_elim:                              0
% 19.36/3.00  pred_elim_cl:                           0
% 19.36/3.00  pred_elim_cycles:                       0
% 19.36/3.00  merged_defs:                            0
% 19.36/3.00  merged_defs_ncl:                        0
% 19.36/3.00  bin_hyper_res:                          0
% 19.36/3.00  prep_cycles:                            2
% 19.36/3.00  pred_elim_time:                         0.
% 19.36/3.00  splitting_time:                         0.
% 19.36/3.00  sem_filter_time:                        0.
% 19.36/3.00  monotx_time:                            0.
% 19.36/3.00  subtype_inf_time:                       0.
% 19.36/3.00  
% 19.36/3.00  ------ Problem properties
% 19.36/3.00  
% 19.36/3.00  clauses:                                9
% 19.36/3.00  conjectures:                            1
% 19.36/3.00  epr:                                    0
% 19.36/3.00  horn:                                   9
% 19.36/3.00  ground:                                 1
% 19.36/3.00  unary:                                  9
% 19.36/3.00  binary:                                 0
% 19.36/3.00  lits:                                   9
% 19.36/3.00  lits_eq:                                9
% 19.36/3.00  fd_pure:                                0
% 19.36/3.00  fd_pseudo:                              0
% 19.36/3.00  fd_cond:                                0
% 19.36/3.00  fd_pseudo_cond:                         0
% 19.36/3.00  ac_symbols:                             0
% 19.36/3.00  
% 19.36/3.00  ------ Propositional Solver
% 19.36/3.00  
% 19.36/3.00  prop_solver_calls:                      13
% 19.36/3.00  prop_fast_solver_calls:                 56
% 19.36/3.00  smt_solver_calls:                       0
% 19.36/3.00  smt_fast_solver_calls:                  0
% 19.36/3.00  prop_num_of_clauses:                    267
% 19.36/3.00  prop_preprocess_simplified:             426
% 19.36/3.00  prop_fo_subsumed:                       0
% 19.36/3.00  prop_solver_time:                       0.
% 19.36/3.00  smt_solver_time:                        0.
% 19.36/3.00  smt_fast_solver_time:                   0.
% 19.36/3.00  prop_fast_solver_time:                  0.
% 19.36/3.00  prop_unsat_core_time:                   0.
% 19.36/3.00  
% 19.36/3.00  ------ QBF
% 19.36/3.00  
% 19.36/3.00  qbf_q_res:                              0
% 19.36/3.00  qbf_num_tautologies:                    0
% 19.36/3.00  qbf_prep_cycles:                        0
% 19.36/3.00  
% 19.36/3.00  ------ BMC1
% 19.36/3.00  
% 19.36/3.00  bmc1_current_bound:                     -1
% 19.36/3.00  bmc1_last_solved_bound:                 -1
% 19.36/3.00  bmc1_unsat_core_size:                   -1
% 19.36/3.00  bmc1_unsat_core_parents_size:           -1
% 19.36/3.00  bmc1_merge_next_fun:                    0
% 19.36/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.36/3.00  
% 19.36/3.00  ------ Instantiation
% 19.36/3.00  
% 19.36/3.00  inst_num_of_clauses:                    0
% 19.36/3.00  inst_num_in_passive:                    0
% 19.36/3.00  inst_num_in_active:                     0
% 19.36/3.00  inst_num_in_unprocessed:                0
% 19.36/3.00  inst_num_of_loops:                      0
% 19.36/3.00  inst_num_of_learning_restarts:          0
% 19.36/3.00  inst_num_moves_active_passive:          0
% 19.36/3.00  inst_lit_activity:                      0
% 19.36/3.00  inst_lit_activity_moves:                0
% 19.36/3.00  inst_num_tautologies:                   0
% 19.36/3.00  inst_num_prop_implied:                  0
% 19.36/3.00  inst_num_existing_simplified:           0
% 19.36/3.00  inst_num_eq_res_simplified:             0
% 19.36/3.00  inst_num_child_elim:                    0
% 19.36/3.00  inst_num_of_dismatching_blockings:      0
% 19.36/3.00  inst_num_of_non_proper_insts:           0
% 19.36/3.00  inst_num_of_duplicates:                 0
% 19.36/3.00  inst_inst_num_from_inst_to_res:         0
% 19.36/3.00  inst_dismatching_checking_time:         0.
% 19.36/3.00  
% 19.36/3.00  ------ Resolution
% 19.36/3.00  
% 19.36/3.00  res_num_of_clauses:                     0
% 19.36/3.00  res_num_in_passive:                     0
% 19.36/3.00  res_num_in_active:                      0
% 19.36/3.00  res_num_of_loops:                       24
% 19.36/3.00  res_forward_subset_subsumed:            0
% 19.36/3.00  res_backward_subset_subsumed:           0
% 19.36/3.00  res_forward_subsumed:                   0
% 19.36/3.00  res_backward_subsumed:                  0
% 19.36/3.00  res_forward_subsumption_resolution:     0
% 19.36/3.00  res_backward_subsumption_resolution:    0
% 19.36/3.00  res_clause_to_clause_subsumption:       70100
% 19.36/3.00  res_orphan_elimination:                 0
% 19.36/3.00  res_tautology_del:                      0
% 19.36/3.00  res_num_eq_res_simplified:              0
% 19.36/3.00  res_num_sel_changes:                    0
% 19.36/3.00  res_moves_from_active_to_pass:          0
% 19.36/3.00  
% 19.36/3.00  ------ Superposition
% 19.36/3.00  
% 19.36/3.00  sup_time_total:                         0.
% 19.36/3.00  sup_time_generating:                    0.
% 19.36/3.00  sup_time_sim_full:                      0.
% 19.36/3.00  sup_time_sim_immed:                     0.
% 19.36/3.00  
% 19.36/3.00  sup_num_of_clauses:                     4291
% 19.36/3.00  sup_num_in_active:                      181
% 19.36/3.00  sup_num_in_passive:                     4110
% 19.36/3.00  sup_num_of_loops:                       197
% 19.36/3.00  sup_fw_superposition:                   9611
% 19.36/3.00  sup_bw_superposition:                   10231
% 19.36/3.00  sup_immediate_simplified:               9511
% 19.36/3.00  sup_given_eliminated:                   2
% 19.36/3.00  comparisons_done:                       0
% 19.36/3.00  comparisons_avoided:                    0
% 19.36/3.00  
% 19.36/3.00  ------ Simplifications
% 19.36/3.00  
% 19.36/3.00  
% 19.36/3.00  sim_fw_subset_subsumed:                 0
% 19.36/3.00  sim_bw_subset_subsumed:                 0
% 19.36/3.00  sim_fw_subsumed:                        696
% 19.36/3.00  sim_bw_subsumed:                        48
% 19.36/3.00  sim_fw_subsumption_res:                 0
% 19.36/3.00  sim_bw_subsumption_res:                 0
% 19.36/3.00  sim_tautology_del:                      0
% 19.36/3.00  sim_eq_tautology_del:                   1005
% 19.36/3.00  sim_eq_res_simp:                        0
% 19.36/3.00  sim_fw_demodulated:                     9233
% 19.36/3.00  sim_bw_demodulated:                     323
% 19.36/3.00  sim_light_normalised:                   993
% 19.36/3.00  sim_joinable_taut:                      0
% 19.36/3.00  sim_joinable_simp:                      0
% 19.36/3.00  sim_ac_normalised:                      0
% 19.36/3.00  sim_smt_subsumption:                    0
% 19.36/3.00  
%------------------------------------------------------------------------------
