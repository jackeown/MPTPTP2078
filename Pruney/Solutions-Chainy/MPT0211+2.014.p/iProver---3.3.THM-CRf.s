%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:25 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 742 expanded)
%              Number of clauses        :   40 (  91 expanded)
%              Number of leaves         :   15 ( 262 expanded)
%              Depth                    :   14
%              Number of atoms          :   84 ( 743 expanded)
%              Number of equality atoms :   83 ( 742 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f29,f45,f41,f41])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f36,f45,f49,f46])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f30,f45,f41])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f37,f45,f41,f47])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) ),
    inference(definition_unfolding,[],[f31,f46,f46])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X1,X1,X3),k5_xboole_0(k1_enumset1(X2,X2,X0),k3_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X3)))) ),
    inference(definition_unfolding,[],[f32,f46,f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2)))) ),
    inference(definition_unfolding,[],[f34,f46,f46])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f44,f45,f41,f41])).

cnf(c_7,plain,
    ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k3_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k1_enumset1(X0_35,X1_35,X2_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_92,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X1_35) ),
    inference(superposition,[status(thm)],[c_27,c_34])).

cnf(c_367,plain,
    ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X0_35,X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_92,c_34])).

cnf(c_409,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_367,c_27])).

cnf(c_8,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X3_35,X4_35),k3_xboole_0(k1_enumset1(X2_35,X3_35,X4_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X4_35),k3_xboole_0(k1_enumset1(X3_35,X3_35,X4_35),k1_enumset1(X0_35,X1_35,X2_35)))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_61,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_26,c_34])).

cnf(c_98,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_27,c_61])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_248,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_27,c_32])).

cnf(c_3,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X0),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X3_35,X3_35,X0_35)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_217,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_31,c_27])).

cnf(c_5,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X3_35,X3_35,X2_35)))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_128,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_29,c_27])).

cnf(c_133,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X1_35,X0_35) ),
    inference(light_normalisation,[status(thm)],[c_128,c_34])).

cnf(c_227,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X1_35,X0_35,X2_35) ),
    inference(light_normalisation,[status(thm)],[c_217,c_133])).

cnf(c_288,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
    inference(light_normalisation,[status(thm)],[c_248,c_227])).

cnf(c_453,plain,
    ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X2_35,X0_35) ),
    inference(light_normalisation,[status(thm)],[c_409,c_98,c_288])).

cnf(c_191,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
    inference(superposition,[status(thm)],[c_27,c_31])).

cnf(c_205,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_31,c_27])).

cnf(c_225,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_31,c_61])).

cnf(c_228,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
    inference(demodulation,[status(thm)],[c_205,c_225])).

cnf(c_229,plain,
    ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X0_35,X2_35) ),
    inference(demodulation,[status(thm)],[c_191,c_227,c_228])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_33,plain,
    ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_46,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK0,sK2,sK0),k1_enumset1(sK1,sK1,sK1)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_26,c_25])).

cnf(c_47,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_33,c_46])).

cnf(c_289,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_229,c_47])).

cnf(c_1058,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_453,c_289])).

cnf(c_48,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(superposition,[status(thm)],[c_33,c_34])).

cnf(c_1059,plain,
    ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1058,c_48])).

cnf(c_1060,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1059])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:13:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.25/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/0.98  
% 2.25/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.25/0.98  
% 2.25/0.98  ------  iProver source info
% 2.25/0.98  
% 2.25/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.25/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.25/0.98  git: non_committed_changes: false
% 2.25/0.98  git: last_make_outside_of_git: false
% 2.25/0.98  
% 2.25/0.98  ------ 
% 2.25/0.98  
% 2.25/0.98  ------ Input Options
% 2.25/0.98  
% 2.25/0.98  --out_options                           all
% 2.25/0.98  --tptp_safe_out                         true
% 2.25/0.98  --problem_path                          ""
% 2.25/0.98  --include_path                          ""
% 2.25/0.98  --clausifier                            res/vclausify_rel
% 2.25/0.98  --clausifier_options                    --mode clausify
% 2.25/0.98  --stdin                                 false
% 2.25/0.98  --stats_out                             all
% 2.25/0.98  
% 2.25/0.98  ------ General Options
% 2.25/0.98  
% 2.25/0.98  --fof                                   false
% 2.25/0.98  --time_out_real                         305.
% 2.25/0.98  --time_out_virtual                      -1.
% 2.25/0.98  --symbol_type_check                     false
% 2.25/0.98  --clausify_out                          false
% 2.25/0.98  --sig_cnt_out                           false
% 2.25/0.98  --trig_cnt_out                          false
% 2.25/0.98  --trig_cnt_out_tolerance                1.
% 2.25/0.98  --trig_cnt_out_sk_spl                   false
% 2.25/0.98  --abstr_cl_out                          false
% 2.25/0.98  
% 2.25/0.98  ------ Global Options
% 2.25/0.98  
% 2.25/0.98  --schedule                              default
% 2.25/0.98  --add_important_lit                     false
% 2.25/0.98  --prop_solver_per_cl                    1000
% 2.25/0.98  --min_unsat_core                        false
% 2.25/0.98  --soft_assumptions                      false
% 2.25/0.98  --soft_lemma_size                       3
% 2.25/0.98  --prop_impl_unit_size                   0
% 2.25/0.98  --prop_impl_unit                        []
% 2.25/0.98  --share_sel_clauses                     true
% 2.25/0.98  --reset_solvers                         false
% 2.25/0.98  --bc_imp_inh                            [conj_cone]
% 2.25/0.98  --conj_cone_tolerance                   3.
% 2.25/0.98  --extra_neg_conj                        none
% 2.25/0.98  --large_theory_mode                     true
% 2.25/0.98  --prolific_symb_bound                   200
% 2.25/0.98  --lt_threshold                          2000
% 2.25/0.98  --clause_weak_htbl                      true
% 2.25/0.98  --gc_record_bc_elim                     false
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing Options
% 2.25/0.98  
% 2.25/0.98  --preprocessing_flag                    true
% 2.25/0.98  --time_out_prep_mult                    0.1
% 2.25/0.98  --splitting_mode                        input
% 2.25/0.98  --splitting_grd                         true
% 2.25/0.98  --splitting_cvd                         false
% 2.25/0.98  --splitting_cvd_svl                     false
% 2.25/0.98  --splitting_nvd                         32
% 2.25/0.98  --sub_typing                            true
% 2.25/0.98  --prep_gs_sim                           true
% 2.25/0.98  --prep_unflatten                        true
% 2.25/0.98  --prep_res_sim                          true
% 2.25/0.98  --prep_upred                            true
% 2.25/0.98  --prep_sem_filter                       exhaustive
% 2.25/0.98  --prep_sem_filter_out                   false
% 2.25/0.98  --pred_elim                             true
% 2.25/0.98  --res_sim_input                         true
% 2.25/0.98  --eq_ax_congr_red                       true
% 2.25/0.98  --pure_diseq_elim                       true
% 2.25/0.98  --brand_transform                       false
% 2.25/0.98  --non_eq_to_eq                          false
% 2.25/0.98  --prep_def_merge                        true
% 2.25/0.98  --prep_def_merge_prop_impl              false
% 2.25/0.98  --prep_def_merge_mbd                    true
% 2.25/0.98  --prep_def_merge_tr_red                 false
% 2.25/0.98  --prep_def_merge_tr_cl                  false
% 2.25/0.98  --smt_preprocessing                     true
% 2.25/0.98  --smt_ac_axioms                         fast
% 2.25/0.98  --preprocessed_out                      false
% 2.25/0.98  --preprocessed_stats                    false
% 2.25/0.98  
% 2.25/0.98  ------ Abstraction refinement Options
% 2.25/0.98  
% 2.25/0.98  --abstr_ref                             []
% 2.25/0.98  --abstr_ref_prep                        false
% 2.25/0.98  --abstr_ref_until_sat                   false
% 2.25/0.98  --abstr_ref_sig_restrict                funpre
% 2.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.98  --abstr_ref_under                       []
% 2.25/0.98  
% 2.25/0.98  ------ SAT Options
% 2.25/0.98  
% 2.25/0.98  --sat_mode                              false
% 2.25/0.98  --sat_fm_restart_options                ""
% 2.25/0.98  --sat_gr_def                            false
% 2.25/0.98  --sat_epr_types                         true
% 2.25/0.98  --sat_non_cyclic_types                  false
% 2.25/0.98  --sat_finite_models                     false
% 2.25/0.98  --sat_fm_lemmas                         false
% 2.25/0.98  --sat_fm_prep                           false
% 2.25/0.98  --sat_fm_uc_incr                        true
% 2.25/0.98  --sat_out_model                         small
% 2.25/0.98  --sat_out_clauses                       false
% 2.25/0.98  
% 2.25/0.98  ------ QBF Options
% 2.25/0.98  
% 2.25/0.98  --qbf_mode                              false
% 2.25/0.98  --qbf_elim_univ                         false
% 2.25/0.98  --qbf_dom_inst                          none
% 2.25/0.98  --qbf_dom_pre_inst                      false
% 2.25/0.98  --qbf_sk_in                             false
% 2.25/0.98  --qbf_pred_elim                         true
% 2.25/0.98  --qbf_split                             512
% 2.25/0.98  
% 2.25/0.98  ------ BMC1 Options
% 2.25/0.98  
% 2.25/0.98  --bmc1_incremental                      false
% 2.25/0.98  --bmc1_axioms                           reachable_all
% 2.25/0.98  --bmc1_min_bound                        0
% 2.25/0.98  --bmc1_max_bound                        -1
% 2.25/0.98  --bmc1_max_bound_default                -1
% 2.25/0.98  --bmc1_symbol_reachability              true
% 2.25/0.98  --bmc1_property_lemmas                  false
% 2.25/0.98  --bmc1_k_induction                      false
% 2.25/0.98  --bmc1_non_equiv_states                 false
% 2.25/0.98  --bmc1_deadlock                         false
% 2.25/0.98  --bmc1_ucm                              false
% 2.25/0.98  --bmc1_add_unsat_core                   none
% 2.25/0.98  --bmc1_unsat_core_children              false
% 2.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.98  --bmc1_out_stat                         full
% 2.25/0.98  --bmc1_ground_init                      false
% 2.25/0.98  --bmc1_pre_inst_next_state              false
% 2.25/0.98  --bmc1_pre_inst_state                   false
% 2.25/0.98  --bmc1_pre_inst_reach_state             false
% 2.25/0.98  --bmc1_out_unsat_core                   false
% 2.25/0.98  --bmc1_aig_witness_out                  false
% 2.25/0.98  --bmc1_verbose                          false
% 2.25/0.98  --bmc1_dump_clauses_tptp                false
% 2.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.98  --bmc1_dump_file                        -
% 2.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.98  --bmc1_ucm_extend_mode                  1
% 2.25/0.98  --bmc1_ucm_init_mode                    2
% 2.25/0.98  --bmc1_ucm_cone_mode                    none
% 2.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.98  --bmc1_ucm_relax_model                  4
% 2.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.98  --bmc1_ucm_layered_model                none
% 2.25/0.98  --bmc1_ucm_max_lemma_size               10
% 2.25/0.98  
% 2.25/0.98  ------ AIG Options
% 2.25/0.98  
% 2.25/0.98  --aig_mode                              false
% 2.25/0.98  
% 2.25/0.98  ------ Instantiation Options
% 2.25/0.98  
% 2.25/0.98  --instantiation_flag                    true
% 2.25/0.98  --inst_sos_flag                         false
% 2.25/0.98  --inst_sos_phase                        true
% 2.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel_side                     num_symb
% 2.25/0.98  --inst_solver_per_active                1400
% 2.25/0.98  --inst_solver_calls_frac                1.
% 2.25/0.98  --inst_passive_queue_type               priority_queues
% 2.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.98  --inst_passive_queues_freq              [25;2]
% 2.25/0.98  --inst_dismatching                      true
% 2.25/0.98  --inst_eager_unprocessed_to_passive     true
% 2.25/0.98  --inst_prop_sim_given                   true
% 2.25/0.98  --inst_prop_sim_new                     false
% 2.25/0.98  --inst_subs_new                         false
% 2.25/0.98  --inst_eq_res_simp                      false
% 2.25/0.98  --inst_subs_given                       false
% 2.25/0.98  --inst_orphan_elimination               true
% 2.25/0.98  --inst_learning_loop_flag               true
% 2.25/0.98  --inst_learning_start                   3000
% 2.25/0.98  --inst_learning_factor                  2
% 2.25/0.98  --inst_start_prop_sim_after_learn       3
% 2.25/0.98  --inst_sel_renew                        solver
% 2.25/0.98  --inst_lit_activity_flag                true
% 2.25/0.98  --inst_restr_to_given                   false
% 2.25/0.98  --inst_activity_threshold               500
% 2.25/0.98  --inst_out_proof                        true
% 2.25/0.98  
% 2.25/0.98  ------ Resolution Options
% 2.25/0.98  
% 2.25/0.98  --resolution_flag                       true
% 2.25/0.98  --res_lit_sel                           adaptive
% 2.25/0.98  --res_lit_sel_side                      none
% 2.25/0.98  --res_ordering                          kbo
% 2.25/0.98  --res_to_prop_solver                    active
% 2.25/0.98  --res_prop_simpl_new                    false
% 2.25/0.98  --res_prop_simpl_given                  true
% 2.25/0.98  --res_passive_queue_type                priority_queues
% 2.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.98  --res_passive_queues_freq               [15;5]
% 2.25/0.98  --res_forward_subs                      full
% 2.25/0.98  --res_backward_subs                     full
% 2.25/0.98  --res_forward_subs_resolution           true
% 2.25/0.98  --res_backward_subs_resolution          true
% 2.25/0.98  --res_orphan_elimination                true
% 2.25/0.98  --res_time_limit                        2.
% 2.25/0.98  --res_out_proof                         true
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Options
% 2.25/0.98  
% 2.25/0.98  --superposition_flag                    true
% 2.25/0.98  --sup_passive_queue_type                priority_queues
% 2.25/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.98  --demod_completeness_check              fast
% 2.25/0.98  --demod_use_ground                      true
% 2.25/0.98  --sup_to_prop_solver                    passive
% 2.25/0.98  --sup_prop_simpl_new                    true
% 2.25/0.98  --sup_prop_simpl_given                  true
% 2.25/0.98  --sup_fun_splitting                     false
% 2.25/0.98  --sup_smt_interval                      50000
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Simplification Setup
% 2.25/0.98  
% 2.25/0.98  --sup_indices_passive                   []
% 2.25/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_full_bw                           [BwDemod]
% 2.25/0.98  --sup_immed_triv                        [TrivRules]
% 2.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_immed_bw_main                     []
% 2.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.98  
% 2.25/0.98  ------ Combination Options
% 2.25/0.98  
% 2.25/0.98  --comb_res_mult                         3
% 2.25/0.98  --comb_sup_mult                         2
% 2.25/0.98  --comb_inst_mult                        10
% 2.25/0.98  
% 2.25/0.98  ------ Debug Options
% 2.25/0.98  
% 2.25/0.98  --dbg_backtrace                         false
% 2.25/0.98  --dbg_dump_prop_clauses                 false
% 2.25/0.98  --dbg_dump_prop_clauses_file            -
% 2.25/0.98  --dbg_out_stat                          false
% 2.25/0.98  ------ Parsing...
% 2.25/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.25/0.98  ------ Proving...
% 2.25/0.98  ------ Problem Properties 
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  clauses                                 10
% 2.25/0.98  conjectures                             1
% 2.25/0.98  EPR                                     0
% 2.25/0.98  Horn                                    10
% 2.25/0.98  unary                                   10
% 2.25/0.98  binary                                  0
% 2.25/0.98  lits                                    10
% 2.25/0.98  lits eq                                 10
% 2.25/0.98  fd_pure                                 0
% 2.25/0.98  fd_pseudo                               0
% 2.25/0.98  fd_cond                                 0
% 2.25/0.98  fd_pseudo_cond                          0
% 2.25/0.98  AC symbols                              0
% 2.25/0.98  
% 2.25/0.98  ------ Schedule UEQ
% 2.25/0.98  
% 2.25/0.98  ------ pure equality problem: resolution off 
% 2.25/0.98  
% 2.25/0.98  ------ Option_UEQ Time Limit: Unbounded
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  ------ 
% 2.25/0.98  Current options:
% 2.25/0.98  ------ 
% 2.25/0.98  
% 2.25/0.98  ------ Input Options
% 2.25/0.98  
% 2.25/0.98  --out_options                           all
% 2.25/0.98  --tptp_safe_out                         true
% 2.25/0.98  --problem_path                          ""
% 2.25/0.98  --include_path                          ""
% 2.25/0.98  --clausifier                            res/vclausify_rel
% 2.25/0.98  --clausifier_options                    --mode clausify
% 2.25/0.98  --stdin                                 false
% 2.25/0.98  --stats_out                             all
% 2.25/0.98  
% 2.25/0.98  ------ General Options
% 2.25/0.98  
% 2.25/0.98  --fof                                   false
% 2.25/0.98  --time_out_real                         305.
% 2.25/0.98  --time_out_virtual                      -1.
% 2.25/0.98  --symbol_type_check                     false
% 2.25/0.98  --clausify_out                          false
% 2.25/0.98  --sig_cnt_out                           false
% 2.25/0.98  --trig_cnt_out                          false
% 2.25/0.98  --trig_cnt_out_tolerance                1.
% 2.25/0.98  --trig_cnt_out_sk_spl                   false
% 2.25/0.98  --abstr_cl_out                          false
% 2.25/0.98  
% 2.25/0.98  ------ Global Options
% 2.25/0.98  
% 2.25/0.98  --schedule                              default
% 2.25/0.98  --add_important_lit                     false
% 2.25/0.98  --prop_solver_per_cl                    1000
% 2.25/0.98  --min_unsat_core                        false
% 2.25/0.98  --soft_assumptions                      false
% 2.25/0.98  --soft_lemma_size                       3
% 2.25/0.98  --prop_impl_unit_size                   0
% 2.25/0.98  --prop_impl_unit                        []
% 2.25/0.98  --share_sel_clauses                     true
% 2.25/0.98  --reset_solvers                         false
% 2.25/0.98  --bc_imp_inh                            [conj_cone]
% 2.25/0.98  --conj_cone_tolerance                   3.
% 2.25/0.98  --extra_neg_conj                        none
% 2.25/0.98  --large_theory_mode                     true
% 2.25/0.98  --prolific_symb_bound                   200
% 2.25/0.98  --lt_threshold                          2000
% 2.25/0.98  --clause_weak_htbl                      true
% 2.25/0.98  --gc_record_bc_elim                     false
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing Options
% 2.25/0.98  
% 2.25/0.98  --preprocessing_flag                    true
% 2.25/0.98  --time_out_prep_mult                    0.1
% 2.25/0.98  --splitting_mode                        input
% 2.25/0.98  --splitting_grd                         true
% 2.25/0.98  --splitting_cvd                         false
% 2.25/0.98  --splitting_cvd_svl                     false
% 2.25/0.98  --splitting_nvd                         32
% 2.25/0.98  --sub_typing                            true
% 2.25/0.98  --prep_gs_sim                           true
% 2.25/0.98  --prep_unflatten                        true
% 2.25/0.98  --prep_res_sim                          true
% 2.25/0.98  --prep_upred                            true
% 2.25/0.98  --prep_sem_filter                       exhaustive
% 2.25/0.98  --prep_sem_filter_out                   false
% 2.25/0.98  --pred_elim                             true
% 2.25/0.98  --res_sim_input                         true
% 2.25/0.98  --eq_ax_congr_red                       true
% 2.25/0.98  --pure_diseq_elim                       true
% 2.25/0.98  --brand_transform                       false
% 2.25/0.98  --non_eq_to_eq                          false
% 2.25/0.98  --prep_def_merge                        true
% 2.25/0.98  --prep_def_merge_prop_impl              false
% 2.25/0.98  --prep_def_merge_mbd                    true
% 2.25/0.98  --prep_def_merge_tr_red                 false
% 2.25/0.98  --prep_def_merge_tr_cl                  false
% 2.25/0.98  --smt_preprocessing                     true
% 2.25/0.98  --smt_ac_axioms                         fast
% 2.25/0.98  --preprocessed_out                      false
% 2.25/0.98  --preprocessed_stats                    false
% 2.25/0.98  
% 2.25/0.98  ------ Abstraction refinement Options
% 2.25/0.98  
% 2.25/0.98  --abstr_ref                             []
% 2.25/0.98  --abstr_ref_prep                        false
% 2.25/0.98  --abstr_ref_until_sat                   false
% 2.25/0.98  --abstr_ref_sig_restrict                funpre
% 2.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.98  --abstr_ref_under                       []
% 2.25/0.98  
% 2.25/0.98  ------ SAT Options
% 2.25/0.98  
% 2.25/0.98  --sat_mode                              false
% 2.25/0.98  --sat_fm_restart_options                ""
% 2.25/0.98  --sat_gr_def                            false
% 2.25/0.98  --sat_epr_types                         true
% 2.25/0.98  --sat_non_cyclic_types                  false
% 2.25/0.98  --sat_finite_models                     false
% 2.25/0.98  --sat_fm_lemmas                         false
% 2.25/0.98  --sat_fm_prep                           false
% 2.25/0.98  --sat_fm_uc_incr                        true
% 2.25/0.98  --sat_out_model                         small
% 2.25/0.98  --sat_out_clauses                       false
% 2.25/0.98  
% 2.25/0.98  ------ QBF Options
% 2.25/0.98  
% 2.25/0.98  --qbf_mode                              false
% 2.25/0.98  --qbf_elim_univ                         false
% 2.25/0.98  --qbf_dom_inst                          none
% 2.25/0.98  --qbf_dom_pre_inst                      false
% 2.25/0.98  --qbf_sk_in                             false
% 2.25/0.98  --qbf_pred_elim                         true
% 2.25/0.98  --qbf_split                             512
% 2.25/0.98  
% 2.25/0.98  ------ BMC1 Options
% 2.25/0.98  
% 2.25/0.98  --bmc1_incremental                      false
% 2.25/0.98  --bmc1_axioms                           reachable_all
% 2.25/0.98  --bmc1_min_bound                        0
% 2.25/0.98  --bmc1_max_bound                        -1
% 2.25/0.98  --bmc1_max_bound_default                -1
% 2.25/0.98  --bmc1_symbol_reachability              true
% 2.25/0.98  --bmc1_property_lemmas                  false
% 2.25/0.98  --bmc1_k_induction                      false
% 2.25/0.98  --bmc1_non_equiv_states                 false
% 2.25/0.98  --bmc1_deadlock                         false
% 2.25/0.98  --bmc1_ucm                              false
% 2.25/0.98  --bmc1_add_unsat_core                   none
% 2.25/0.98  --bmc1_unsat_core_children              false
% 2.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.98  --bmc1_out_stat                         full
% 2.25/0.98  --bmc1_ground_init                      false
% 2.25/0.98  --bmc1_pre_inst_next_state              false
% 2.25/0.98  --bmc1_pre_inst_state                   false
% 2.25/0.98  --bmc1_pre_inst_reach_state             false
% 2.25/0.98  --bmc1_out_unsat_core                   false
% 2.25/0.98  --bmc1_aig_witness_out                  false
% 2.25/0.98  --bmc1_verbose                          false
% 2.25/0.98  --bmc1_dump_clauses_tptp                false
% 2.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.98  --bmc1_dump_file                        -
% 2.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.98  --bmc1_ucm_extend_mode                  1
% 2.25/0.98  --bmc1_ucm_init_mode                    2
% 2.25/0.98  --bmc1_ucm_cone_mode                    none
% 2.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.98  --bmc1_ucm_relax_model                  4
% 2.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.98  --bmc1_ucm_layered_model                none
% 2.25/0.98  --bmc1_ucm_max_lemma_size               10
% 2.25/0.98  
% 2.25/0.98  ------ AIG Options
% 2.25/0.98  
% 2.25/0.98  --aig_mode                              false
% 2.25/0.98  
% 2.25/0.98  ------ Instantiation Options
% 2.25/0.98  
% 2.25/0.98  --instantiation_flag                    false
% 2.25/0.98  --inst_sos_flag                         false
% 2.25/0.98  --inst_sos_phase                        true
% 2.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel_side                     num_symb
% 2.25/0.98  --inst_solver_per_active                1400
% 2.25/0.98  --inst_solver_calls_frac                1.
% 2.25/0.98  --inst_passive_queue_type               priority_queues
% 2.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.98  --inst_passive_queues_freq              [25;2]
% 2.25/0.98  --inst_dismatching                      true
% 2.25/0.98  --inst_eager_unprocessed_to_passive     true
% 2.25/0.98  --inst_prop_sim_given                   true
% 2.25/0.98  --inst_prop_sim_new                     false
% 2.25/0.98  --inst_subs_new                         false
% 2.25/0.98  --inst_eq_res_simp                      false
% 2.25/0.98  --inst_subs_given                       false
% 2.25/0.98  --inst_orphan_elimination               true
% 2.25/0.98  --inst_learning_loop_flag               true
% 2.25/0.98  --inst_learning_start                   3000
% 2.25/0.98  --inst_learning_factor                  2
% 2.25/0.98  --inst_start_prop_sim_after_learn       3
% 2.25/0.98  --inst_sel_renew                        solver
% 2.25/0.98  --inst_lit_activity_flag                true
% 2.25/0.98  --inst_restr_to_given                   false
% 2.25/0.98  --inst_activity_threshold               500
% 2.25/0.98  --inst_out_proof                        true
% 2.25/0.98  
% 2.25/0.98  ------ Resolution Options
% 2.25/0.98  
% 2.25/0.98  --resolution_flag                       false
% 2.25/0.98  --res_lit_sel                           adaptive
% 2.25/0.98  --res_lit_sel_side                      none
% 2.25/0.98  --res_ordering                          kbo
% 2.25/0.98  --res_to_prop_solver                    active
% 2.25/0.98  --res_prop_simpl_new                    false
% 2.25/0.98  --res_prop_simpl_given                  true
% 2.25/0.98  --res_passive_queue_type                priority_queues
% 2.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.98  --res_passive_queues_freq               [15;5]
% 2.25/0.98  --res_forward_subs                      full
% 2.25/0.98  --res_backward_subs                     full
% 2.25/0.98  --res_forward_subs_resolution           true
% 2.25/0.98  --res_backward_subs_resolution          true
% 2.25/0.98  --res_orphan_elimination                true
% 2.25/0.98  --res_time_limit                        2.
% 2.25/0.98  --res_out_proof                         true
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Options
% 2.25/0.98  
% 2.25/0.98  --superposition_flag                    true
% 2.25/0.98  --sup_passive_queue_type                priority_queues
% 2.25/0.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.98  --demod_completeness_check              fast
% 2.25/0.98  --demod_use_ground                      true
% 2.25/0.98  --sup_to_prop_solver                    active
% 2.25/0.98  --sup_prop_simpl_new                    false
% 2.25/0.98  --sup_prop_simpl_given                  false
% 2.25/0.98  --sup_fun_splitting                     true
% 2.25/0.98  --sup_smt_interval                      10000
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Simplification Setup
% 2.25/0.98  
% 2.25/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.25/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_full_triv                         [TrivRules]
% 2.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.25/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.25/0.98  --sup_immed_triv                        [TrivRules]
% 2.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.98  --sup_immed_bw_main                     []
% 2.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.25/0.98  
% 2.25/0.98  ------ Combination Options
% 2.25/0.98  
% 2.25/0.98  --comb_res_mult                         1
% 2.25/0.98  --comb_sup_mult                         1
% 2.25/0.98  --comb_inst_mult                        1000000
% 2.25/0.98  
% 2.25/0.98  ------ Debug Options
% 2.25/0.98  
% 2.25/0.98  --dbg_backtrace                         false
% 2.25/0.98  --dbg_dump_prop_clauses                 false
% 2.25/0.98  --dbg_dump_prop_clauses_file            -
% 2.25/0.98  --dbg_out_stat                          false
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  ------ Proving...
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  % SZS status Theorem for theBenchmark.p
% 2.25/0.98  
% 2.25/0.98   Resolution empty clause
% 2.25/0.98  
% 2.25/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.25/0.98  
% 2.25/0.98  fof(f12,axiom,(
% 2.25/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f36,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f12])).
% 2.25/0.98  
% 2.25/0.98  fof(f16,axiom,(
% 2.25/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f40,plain,(
% 2.25/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f16])).
% 2.25/0.98  
% 2.25/0.98  fof(f49,plain,(
% 2.25/0.98    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 2.25/0.98    inference(definition_unfolding,[],[f40,f41])).
% 2.25/0.98  
% 2.25/0.98  fof(f5,axiom,(
% 2.25/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f29,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f5])).
% 2.25/0.98  
% 2.25/0.98  fof(f3,axiom,(
% 2.25/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f27,plain,(
% 2.25/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f3])).
% 2.25/0.98  
% 2.25/0.98  fof(f2,axiom,(
% 2.25/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f26,plain,(
% 2.25/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.25/0.98    inference(cnf_transformation,[],[f2])).
% 2.25/0.98  
% 2.25/0.98  fof(f45,plain,(
% 2.25/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.25/0.98    inference(definition_unfolding,[],[f27,f26])).
% 2.25/0.98  
% 2.25/0.98  fof(f17,axiom,(
% 2.25/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f41,plain,(
% 2.25/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f17])).
% 2.25/0.98  
% 2.25/0.98  fof(f46,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.25/0.98    inference(definition_unfolding,[],[f29,f45,f41,f41])).
% 2.25/0.98  
% 2.25/0.98  fof(f58,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2))))) )),
% 2.25/0.98    inference(definition_unfolding,[],[f36,f45,f49,f46])).
% 2.25/0.98  
% 2.25/0.98  fof(f18,axiom,(
% 2.25/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f42,plain,(
% 2.25/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f18])).
% 2.25/0.98  
% 2.25/0.98  fof(f52,plain,(
% 2.25/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 2.25/0.98    inference(definition_unfolding,[],[f42,f46])).
% 2.25/0.98  
% 2.25/0.98  fof(f13,axiom,(
% 2.25/0.98    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f37,plain,(
% 2.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f13])).
% 2.25/0.98  
% 2.25/0.98  fof(f6,axiom,(
% 2.25/0.98    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f30,plain,(
% 2.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f6])).
% 2.25/0.98  
% 2.25/0.98  fof(f47,plain,(
% 2.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.25/0.98    inference(definition_unfolding,[],[f30,f45,f41])).
% 2.25/0.98  
% 2.25/0.98  fof(f59,plain,(
% 2.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))))) )),
% 2.25/0.98    inference(definition_unfolding,[],[f37,f45,f41,f47])).
% 2.25/0.98  
% 2.25/0.98  fof(f7,axiom,(
% 2.25/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f31,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f7])).
% 2.25/0.98  
% 2.25/0.98  fof(f53,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))))) )),
% 2.25/0.98    inference(definition_unfolding,[],[f31,f46,f46])).
% 2.25/0.98  
% 2.25/0.98  fof(f8,axiom,(
% 2.25/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f32,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f8])).
% 2.25/0.98  
% 2.25/0.98  fof(f54,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X1,X1,X3),k5_xboole_0(k1_enumset1(X2,X2,X0),k3_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X3))))) )),
% 2.25/0.98    inference(definition_unfolding,[],[f32,f46,f46])).
% 2.25/0.98  
% 2.25/0.98  fof(f10,axiom,(
% 2.25/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f34,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f10])).
% 2.25/0.98  
% 2.25/0.98  fof(f56,plain,(
% 2.25/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2))))) )),
% 2.25/0.98    inference(definition_unfolding,[],[f34,f46,f46])).
% 2.25/0.98  
% 2.25/0.98  fof(f1,axiom,(
% 2.25/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f25,plain,(
% 2.25/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f1])).
% 2.25/0.98  
% 2.25/0.98  fof(f20,conjecture,(
% 2.25/0.98    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f21,negated_conjecture,(
% 2.25/0.98    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.25/0.98    inference(negated_conjecture,[],[f20])).
% 2.25/0.98  
% 2.25/0.98  fof(f22,plain,(
% 2.25/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.25/0.98    inference(ennf_transformation,[],[f21])).
% 2.25/0.98  
% 2.25/0.98  fof(f23,plain,(
% 2.25/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.25/0.98    introduced(choice_axiom,[])).
% 2.25/0.98  
% 2.25/0.98  fof(f24,plain,(
% 2.25/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 2.25/0.98  
% 2.25/0.98  fof(f44,plain,(
% 2.25/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.25/0.98    inference(cnf_transformation,[],[f24])).
% 2.25/0.98  
% 2.25/0.98  fof(f61,plain,(
% 2.25/0.98    k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2)),
% 2.25/0.98    inference(definition_unfolding,[],[f44,f45,f41,f41])).
% 2.25/0.98  
% 2.25/0.98  cnf(c_7,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
% 2.25/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_27,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k3_xboole_0(k1_enumset1(X3_35,X3_35,X3_35),k1_enumset1(X0_35,X1_35,X2_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_0,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
% 2.25/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_34,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_92,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X0_35,X1_35,X1_35) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_27,c_34]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_367,plain,
% 2.25/0.98      ( k1_enumset1(X0_35,X1_35,X1_35) = k1_enumset1(X0_35,X0_35,X1_35) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_92,c_34]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_409,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_367,c_27]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_8,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))) ),
% 2.25/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_26,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X3_35,X4_35),k3_xboole_0(k1_enumset1(X2_35,X3_35,X4_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X4_35),k3_xboole_0(k1_enumset1(X3_35,X3_35,X4_35),k1_enumset1(X0_35,X1_35,X2_35)))) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_61,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_26,c_34]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_98,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X1_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X1_35,X1_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_27,c_61]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_2,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) ),
% 2.25/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_32,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_248,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X0_35)))) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_27,c_32]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_3,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X0),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0)))) ),
% 2.25/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_31,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X3_35,X3_35,X0_35)))) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_217,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_31,c_27]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_5,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X3,X3,X2),k5_xboole_0(k1_enumset1(X1,X1,X0),k3_xboole_0(k1_enumset1(X1,X1,X0),k1_enumset1(X3,X3,X2)))) ),
% 2.25/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_29,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X3_35,X3_35,X2_35)))) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_128,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X0_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_29,c_27]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_133,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X1_35,X0_35) ),
% 2.25/0.98      inference(light_normalisation,[status(thm)],[c_128,c_34]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_227,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X1_35,X0_35,X2_35) ),
% 2.25/0.98      inference(light_normalisation,[status(thm)],[c_217,c_133]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_288,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
% 2.25/0.98      inference(light_normalisation,[status(thm)],[c_248,c_227]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_453,plain,
% 2.25/0.98      ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X2_35,X0_35) ),
% 2.25/0.98      inference(light_normalisation,[status(thm)],[c_409,c_98,c_288]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_191,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X2_35)))) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_27,c_31]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_205,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_31,c_27]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_225,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_31,c_61]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_228,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k1_enumset1(X0_35,X0_35,X0_35)))) = k1_enumset1(X1_35,X2_35,X0_35) ),
% 2.25/0.98      inference(demodulation,[status(thm)],[c_205,c_225]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_229,plain,
% 2.25/0.98      ( k1_enumset1(X0_35,X1_35,X2_35) = k1_enumset1(X1_35,X0_35,X2_35) ),
% 2.25/0.98      inference(demodulation,[status(thm)],[c_191,c_227,c_228]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_1,plain,
% 2.25/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.25/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_33,plain,
% 2.25/0.98      ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_10,negated_conjecture,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.25/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_25,negated_conjecture,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.25/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_46,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK0,sK2,sK0),k1_enumset1(sK1,sK1,sK1)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.25/0.98      inference(demodulation,[status(thm)],[c_26,c_25]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_47,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.25/0.98      inference(demodulation,[status(thm)],[c_33,c_46]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_289,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK0)))) != k1_enumset1(sK1,sK0,sK2) ),
% 2.25/0.98      inference(demodulation,[status(thm)],[c_229,c_47]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_1058,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK0,sK2)))) != k1_enumset1(sK1,sK0,sK2) ),
% 2.25/0.98      inference(demodulation,[status(thm)],[c_453,c_289]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_48,plain,
% 2.25/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.25/0.98      inference(superposition,[status(thm)],[c_33,c_34]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_1059,plain,
% 2.25/0.98      ( k1_enumset1(sK1,sK0,sK2) != k1_enumset1(sK1,sK0,sK2) ),
% 2.25/0.98      inference(demodulation,[status(thm)],[c_1058,c_48]) ).
% 2.25/0.98  
% 2.25/0.98  cnf(c_1060,plain,
% 2.25/0.98      ( $false ),
% 2.25/0.98      inference(equality_resolution_simp,[status(thm)],[c_1059]) ).
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.25/0.98  
% 2.25/0.98  ------                               Statistics
% 2.25/0.98  
% 2.25/0.98  ------ General
% 2.25/0.98  
% 2.25/0.98  abstr_ref_over_cycles:                  0
% 2.25/0.98  abstr_ref_under_cycles:                 0
% 2.25/0.98  gc_basic_clause_elim:                   0
% 2.25/0.98  forced_gc_time:                         0
% 2.25/0.98  parsing_time:                           0.01
% 2.25/0.98  unif_index_cands_time:                  0.
% 2.25/0.98  unif_index_add_time:                    0.
% 2.25/0.98  orderings_time:                         0.
% 2.25/0.98  out_proof_time:                         0.007
% 2.25/0.98  total_time:                             0.182
% 2.25/0.98  num_of_symbols:                         39
% 2.25/0.98  num_of_terms:                           5412
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing
% 2.25/0.98  
% 2.25/0.98  num_of_splits:                          0
% 2.25/0.98  num_of_split_atoms:                     0
% 2.25/0.98  num_of_reused_defs:                     0
% 2.25/0.98  num_eq_ax_congr_red:                    3
% 2.25/0.98  num_of_sem_filtered_clauses:            0
% 2.25/0.98  num_of_subtypes:                        2
% 2.25/0.98  monotx_restored_types:                  0
% 2.25/0.98  sat_num_of_epr_types:                   0
% 2.25/0.98  sat_num_of_non_cyclic_types:            0
% 2.25/0.98  sat_guarded_non_collapsed_types:        0
% 2.25/0.98  num_pure_diseq_elim:                    0
% 2.25/0.98  simp_replaced_by:                       0
% 2.25/0.98  res_preprocessed:                       34
% 2.25/0.98  prep_upred:                             0
% 2.25/0.98  prep_unflattend:                        0
% 2.25/0.98  smt_new_axioms:                         0
% 2.25/0.98  pred_elim_cands:                        0
% 2.25/0.98  pred_elim:                              0
% 2.25/0.98  pred_elim_cl:                           0
% 2.25/0.98  pred_elim_cycles:                       0
% 2.25/0.98  merged_defs:                            0
% 2.25/0.98  merged_defs_ncl:                        0
% 2.25/0.98  bin_hyper_res:                          0
% 2.25/0.98  prep_cycles:                            3
% 2.25/0.98  pred_elim_time:                         0.
% 2.25/0.98  splitting_time:                         0.
% 2.25/0.98  sem_filter_time:                        0.
% 2.25/0.98  monotx_time:                            0.
% 2.25/0.98  subtype_inf_time:                       0.001
% 2.25/0.98  
% 2.25/0.98  ------ Problem properties
% 2.25/0.98  
% 2.25/0.98  clauses:                                10
% 2.25/0.98  conjectures:                            1
% 2.25/0.98  epr:                                    0
% 2.25/0.98  horn:                                   10
% 2.25/0.98  ground:                                 1
% 2.25/0.98  unary:                                  10
% 2.25/0.98  binary:                                 0
% 2.25/0.98  lits:                                   10
% 2.25/0.98  lits_eq:                                10
% 2.25/0.98  fd_pure:                                0
% 2.25/0.98  fd_pseudo:                              0
% 2.25/0.98  fd_cond:                                0
% 2.25/0.98  fd_pseudo_cond:                         0
% 2.25/0.98  ac_symbols:                             0
% 2.25/0.98  
% 2.25/0.98  ------ Propositional Solver
% 2.25/0.98  
% 2.25/0.98  prop_solver_calls:                      17
% 2.25/0.98  prop_fast_solver_calls:                 80
% 2.25/0.98  smt_solver_calls:                       0
% 2.25/0.98  smt_fast_solver_calls:                  0
% 2.25/0.98  prop_num_of_clauses:                    54
% 2.25/0.98  prop_preprocess_simplified:             456
% 2.25/0.98  prop_fo_subsumed:                       0
% 2.25/0.98  prop_solver_time:                       0.
% 2.25/0.98  smt_solver_time:                        0.
% 2.25/0.98  smt_fast_solver_time:                   0.
% 2.25/0.98  prop_fast_solver_time:                  0.
% 2.25/0.98  prop_unsat_core_time:                   0.
% 2.25/0.98  
% 2.25/0.98  ------ QBF
% 2.25/0.98  
% 2.25/0.98  qbf_q_res:                              0
% 2.25/0.98  qbf_num_tautologies:                    0
% 2.25/0.98  qbf_prep_cycles:                        0
% 2.25/0.98  
% 2.25/0.98  ------ BMC1
% 2.25/0.98  
% 2.25/0.98  bmc1_current_bound:                     -1
% 2.25/0.98  bmc1_last_solved_bound:                 -1
% 2.25/0.98  bmc1_unsat_core_size:                   -1
% 2.25/0.98  bmc1_unsat_core_parents_size:           -1
% 2.25/0.98  bmc1_merge_next_fun:                    0
% 2.25/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.25/0.98  
% 2.25/0.98  ------ Instantiation
% 2.25/0.98  
% 2.25/0.98  inst_num_of_clauses:                    0
% 2.25/0.98  inst_num_in_passive:                    0
% 2.25/0.98  inst_num_in_active:                     0
% 2.25/0.98  inst_num_in_unprocessed:                0
% 2.25/0.98  inst_num_of_loops:                      0
% 2.25/0.98  inst_num_of_learning_restarts:          0
% 2.25/0.98  inst_num_moves_active_passive:          0
% 2.25/0.98  inst_lit_activity:                      0
% 2.25/0.98  inst_lit_activity_moves:                0
% 2.25/0.98  inst_num_tautologies:                   0
% 2.25/0.98  inst_num_prop_implied:                  0
% 2.25/0.98  inst_num_existing_simplified:           0
% 2.25/0.98  inst_num_eq_res_simplified:             0
% 2.25/0.98  inst_num_child_elim:                    0
% 2.25/0.98  inst_num_of_dismatching_blockings:      0
% 2.25/0.98  inst_num_of_non_proper_insts:           0
% 2.25/0.98  inst_num_of_duplicates:                 0
% 2.25/0.98  inst_inst_num_from_inst_to_res:         0
% 2.25/0.98  inst_dismatching_checking_time:         0.
% 2.25/0.98  
% 2.25/0.98  ------ Resolution
% 2.25/0.98  
% 2.25/0.98  res_num_of_clauses:                     0
% 2.25/0.98  res_num_in_passive:                     0
% 2.25/0.98  res_num_in_active:                      0
% 2.25/0.98  res_num_of_loops:                       37
% 2.25/0.98  res_forward_subset_subsumed:            0
% 2.25/0.98  res_backward_subset_subsumed:           0
% 2.25/0.98  res_forward_subsumed:                   0
% 2.25/0.98  res_backward_subsumed:                  0
% 2.25/0.98  res_forward_subsumption_resolution:     0
% 2.25/0.98  res_backward_subsumption_resolution:    0
% 2.25/0.98  res_clause_to_clause_subsumption:       5173
% 2.25/0.98  res_orphan_elimination:                 0
% 2.25/0.98  res_tautology_del:                      1
% 2.25/0.98  res_num_eq_res_simplified:              0
% 2.25/0.98  res_num_sel_changes:                    0
% 2.25/0.98  res_moves_from_active_to_pass:          0
% 2.25/0.98  
% 2.25/0.98  ------ Superposition
% 2.25/0.98  
% 2.25/0.98  sup_time_total:                         0.
% 2.25/0.98  sup_time_generating:                    0.
% 2.25/0.98  sup_time_sim_full:                      0.
% 2.25/0.98  sup_time_sim_immed:                     0.
% 2.25/0.98  
% 2.25/0.98  sup_num_of_clauses:                     254
% 2.25/0.98  sup_num_in_active:                      23
% 2.25/0.98  sup_num_in_passive:                     231
% 2.25/0.98  sup_num_of_loops:                       26
% 2.25/0.98  sup_fw_superposition:                   544
% 2.25/0.98  sup_bw_superposition:                   388
% 2.25/0.98  sup_immediate_simplified:               95
% 2.25/0.98  sup_given_eliminated:                   0
% 2.25/0.98  comparisons_done:                       0
% 2.25/0.98  comparisons_avoided:                    0
% 2.25/0.98  
% 2.25/0.98  ------ Simplifications
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  sim_fw_subset_subsumed:                 0
% 2.25/0.98  sim_bw_subset_subsumed:                 0
% 2.25/0.98  sim_fw_subsumed:                        11
% 2.25/0.98  sim_bw_subsumed:                        8
% 2.25/0.98  sim_fw_subsumption_res:                 0
% 2.25/0.98  sim_bw_subsumption_res:                 0
% 2.25/0.98  sim_tautology_del:                      0
% 2.25/0.98  sim_eq_tautology_del:                   1
% 2.25/0.98  sim_eq_res_simp:                        0
% 2.25/0.98  sim_fw_demodulated:                     46
% 2.25/0.98  sim_bw_demodulated:                     4
% 2.25/0.98  sim_light_normalised:                   31
% 2.25/0.98  sim_joinable_taut:                      0
% 2.25/0.98  sim_joinable_simp:                      0
% 2.25/0.98  sim_ac_normalised:                      0
% 2.25/0.98  sim_smt_subsumption:                    0
% 2.25/0.98  
%------------------------------------------------------------------------------
