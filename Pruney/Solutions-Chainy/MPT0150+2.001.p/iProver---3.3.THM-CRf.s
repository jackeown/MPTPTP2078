%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:44 EST 2020

% Result     : Theorem 43.37s
% Output     : CNFRefutation 43.37s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 360 expanded)
%              Number of clauses        :   20 (  59 expanded)
%              Number of leaves         :   12 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :   57 ( 361 expanded)
%              Number of equality atoms :   56 ( 360 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f16,f18,f18])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f21,f18])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f22,f18,f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f20,f18,f27])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f23,f18,f28])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f24,f18,f30,f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f17,f18,f18,f18,f18])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))))),k1_tarski(X0))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f25,f18,f31])).

fof(f36,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f26,f18,f29,f28,f32])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,plain,
    ( k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)) = k5_xboole_0(X1_40,k4_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k4_xboole_0(k1_tarski(X6_42),k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k1_tarski(X2_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k4_xboole_0(k2_enumset1(X3_42,X4_42,X5_42,X6_42),k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k1_tarski(X2_42),k1_tarski(X1_42))),k1_tarski(X0_42))))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),k4_xboole_0(X2_40,k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)))) = k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_33,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k4_xboole_0(k1_tarski(X6_42),k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))))) = k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k5_xboole_0(k1_tarski(X2_42),k4_xboole_0(k2_enumset1(X3_42,X4_42,X5_42,X6_42),k1_tarski(X2_42))),k1_tarski(X1_42))),k1_tarski(X0_42))) ),
    inference(demodulation,[status(thm)],[c_14,c_15])).

cnf(c_549,plain,
    ( k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k5_xboole_0(k1_tarski(X2_42),k4_xboole_0(k2_enumset1(X3_42,X4_42,X5_42,X6_42),k1_tarski(X2_42))),k1_tarski(X1_42))),k1_tarski(X0_42))) = k5_xboole_0(k1_tarski(X6_42),k4_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k1_tarski(X6_42))) ),
    inference(superposition,[status(thm)],[c_16,c_33])).

cnf(c_107,plain,
    ( k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) = k5_xboole_0(X2_40,k4_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),X2_40)) ),
    inference(superposition,[status(thm)],[c_16,c_15])).

cnf(c_138,plain,
    ( k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) = k5_xboole_0(X1_40,k4_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X2_40,X0_40)),X1_40)) ),
    inference(superposition,[status(thm)],[c_16,c_107])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_36,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_13,c_15])).

cnf(c_37,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_36,c_15])).

cnf(c_287,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK5))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_138,c_37])).

cnf(c_453,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(superposition,[status(thm)],[c_107,c_287])).

cnf(c_44927,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k2_enumset1(sK7,sK1,sK2,sK3),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_549,c_453])).

cnf(c_57781,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k2_enumset1(sK6,sK7,sK1,sK2),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(superposition,[status(thm)],[c_549,c_44927])).

cnf(c_57941,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_enumset1(sK5,sK6,sK7,sK1),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(superposition,[status(thm)],[c_549,c_57781])).

cnf(c_57943,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_549,c_57941])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.37/5.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.37/5.99  
% 43.37/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.37/5.99  
% 43.37/5.99  ------  iProver source info
% 43.37/5.99  
% 43.37/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.37/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.37/5.99  git: non_committed_changes: false
% 43.37/5.99  git: last_make_outside_of_git: false
% 43.37/5.99  
% 43.37/5.99  ------ 
% 43.37/5.99  ------ Parsing...
% 43.37/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.37/5.99  
% 43.37/5.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 43.37/5.99  
% 43.37/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.37/5.99  
% 43.37/5.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/5.99  ------ Proving...
% 43.37/5.99  ------ Problem Properties 
% 43.37/5.99  
% 43.37/5.99  
% 43.37/5.99  clauses                                 4
% 43.37/5.99  conjectures                             1
% 43.37/5.99  EPR                                     0
% 43.37/5.99  Horn                                    4
% 43.37/5.99  unary                                   4
% 43.37/5.99  binary                                  0
% 43.37/5.99  lits                                    4
% 43.37/5.99  lits eq                                 4
% 43.37/5.99  fd_pure                                 0
% 43.37/5.99  fd_pseudo                               0
% 43.37/5.99  fd_cond                                 0
% 43.37/5.99  fd_pseudo_cond                          0
% 43.37/5.99  AC symbols                              0
% 43.37/5.99  
% 43.37/5.99  ------ Input Options Time Limit: Unbounded
% 43.37/5.99  
% 43.37/5.99  
% 43.37/5.99  ------ 
% 43.37/5.99  Current options:
% 43.37/5.99  ------ 
% 43.37/5.99  
% 43.37/5.99  
% 43.37/5.99  
% 43.37/5.99  
% 43.37/5.99  ------ Proving...
% 43.37/5.99  
% 43.37/5.99  
% 43.37/5.99  % SZS status Theorem for theBenchmark.p
% 43.37/5.99  
% 43.37/5.99   Resolution empty clause
% 43.37/5.99  
% 43.37/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.37/5.99  
% 43.37/5.99  fof(f1,axiom,(
% 43.37/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f16,plain,(
% 43.37/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f1])).
% 43.37/5.99  
% 43.37/5.99  fof(f3,axiom,(
% 43.37/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f18,plain,(
% 43.37/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 43.37/5.99    inference(cnf_transformation,[],[f3])).
% 43.37/5.99  
% 43.37/5.99  fof(f33,plain,(
% 43.37/5.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 43.37/5.99    inference(definition_unfolding,[],[f16,f18,f18])).
% 43.37/5.99  
% 43.37/5.99  fof(f9,axiom,(
% 43.37/5.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f24,plain,(
% 43.37/5.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f9])).
% 43.37/5.99  
% 43.37/5.99  fof(f7,axiom,(
% 43.37/5.99    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f22,plain,(
% 43.37/5.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f7])).
% 43.37/5.99  
% 43.37/5.99  fof(f6,axiom,(
% 43.37/5.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f21,plain,(
% 43.37/5.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f6])).
% 43.37/5.99  
% 43.37/5.99  fof(f29,plain,(
% 43.37/5.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.37/5.99    inference(definition_unfolding,[],[f21,f18])).
% 43.37/5.99  
% 43.37/5.99  fof(f30,plain,(
% 43.37/5.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 43.37/5.99    inference(definition_unfolding,[],[f22,f18,f29])).
% 43.37/5.99  
% 43.37/5.99  fof(f8,axiom,(
% 43.37/5.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f23,plain,(
% 43.37/5.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f8])).
% 43.37/5.99  
% 43.37/5.99  fof(f5,axiom,(
% 43.37/5.99    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f20,plain,(
% 43.37/5.99    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f5])).
% 43.37/5.99  
% 43.37/5.99  fof(f4,axiom,(
% 43.37/5.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f19,plain,(
% 43.37/5.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f4])).
% 43.37/5.99  
% 43.37/5.99  fof(f27,plain,(
% 43.37/5.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 43.37/5.99    inference(definition_unfolding,[],[f19,f18])).
% 43.37/5.99  
% 43.37/5.99  fof(f28,plain,(
% 43.37/5.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 43.37/5.99    inference(definition_unfolding,[],[f20,f18,f27])).
% 43.37/5.99  
% 43.37/5.99  fof(f31,plain,(
% 43.37/5.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 43.37/5.99    inference(definition_unfolding,[],[f23,f18,f28])).
% 43.37/5.99  
% 43.37/5.99  fof(f35,plain,(
% 43.37/5.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0)))))) )),
% 43.37/5.99    inference(definition_unfolding,[],[f24,f18,f30,f31])).
% 43.37/5.99  
% 43.37/5.99  fof(f2,axiom,(
% 43.37/5.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f17,plain,(
% 43.37/5.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f2])).
% 43.37/5.99  
% 43.37/5.99  fof(f34,plain,(
% 43.37/5.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 43.37/5.99    inference(definition_unfolding,[],[f17,f18,f18,f18,f18])).
% 43.37/5.99  
% 43.37/5.99  fof(f11,conjecture,(
% 43.37/5.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f12,negated_conjecture,(
% 43.37/5.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 43.37/5.99    inference(negated_conjecture,[],[f11])).
% 43.37/5.99  
% 43.37/5.99  fof(f13,plain,(
% 43.37/5.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 43.37/5.99    inference(ennf_transformation,[],[f12])).
% 43.37/5.99  
% 43.37/5.99  fof(f14,plain,(
% 43.37/5.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) => k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 43.37/5.99    introduced(choice_axiom,[])).
% 43.37/5.99  
% 43.37/5.99  fof(f15,plain,(
% 43.37/5.99    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 43.37/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).
% 43.37/5.99  
% 43.37/5.99  fof(f26,plain,(
% 43.37/5.99    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 43.37/5.99    inference(cnf_transformation,[],[f15])).
% 43.37/5.99  
% 43.37/5.99  fof(f10,axiom,(
% 43.37/5.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 43.37/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.37/5.99  
% 43.37/5.99  fof(f25,plain,(
% 43.37/5.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 43.37/5.99    inference(cnf_transformation,[],[f10])).
% 43.37/5.99  
% 43.37/5.99  fof(f32,plain,(
% 43.37/5.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))))),k1_tarski(X0))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 43.37/5.99    inference(definition_unfolding,[],[f25,f18,f31])).
% 43.37/5.99  
% 43.37/5.99  fof(f36,plain,(
% 43.37/5.99    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0)))),
% 43.37/5.99    inference(definition_unfolding,[],[f26,f18,f29,f28,f32])).
% 43.37/5.99  
% 43.37/5.99  cnf(c_0,plain,
% 43.37/5.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 43.37/5.99      inference(cnf_transformation,[],[f33]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_16,plain,
% 43.37/5.99      ( k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)) = k5_xboole_0(X1_40,k4_xboole_0(X0_40,X1_40)) ),
% 43.37/5.99      inference(subtyping,[status(esa)],[c_0]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_2,plain,
% 43.37/5.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) ),
% 43.37/5.99      inference(cnf_transformation,[],[f35]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_14,plain,
% 43.37/5.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k4_xboole_0(k1_tarski(X6_42),k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k1_tarski(X2_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k4_xboole_0(k2_enumset1(X3_42,X4_42,X5_42,X6_42),k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k1_tarski(X2_42),k1_tarski(X1_42))),k1_tarski(X0_42))))) ),
% 43.37/5.99      inference(subtyping,[status(esa)],[c_2]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_1,plain,
% 43.37/5.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 43.37/5.99      inference(cnf_transformation,[],[f34]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_15,plain,
% 43.37/5.99      ( k5_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),k4_xboole_0(X2_40,k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)))) = k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) ),
% 43.37/5.99      inference(subtyping,[status(esa)],[c_1]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_33,plain,
% 43.37/5.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k4_xboole_0(k1_tarski(X6_42),k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))))) = k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k5_xboole_0(k1_tarski(X2_42),k4_xboole_0(k2_enumset1(X3_42,X4_42,X5_42,X6_42),k1_tarski(X2_42))),k1_tarski(X1_42))),k1_tarski(X0_42))) ),
% 43.37/5.99      inference(demodulation,[status(thm)],[c_14,c_15]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_549,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k5_xboole_0(k1_tarski(X2_42),k4_xboole_0(k2_enumset1(X3_42,X4_42,X5_42,X6_42),k1_tarski(X2_42))),k1_tarski(X1_42))),k1_tarski(X0_42))) = k5_xboole_0(k1_tarski(X6_42),k4_xboole_0(k5_xboole_0(k1_tarski(X0_42),k4_xboole_0(k5_xboole_0(k1_tarski(X1_42),k4_xboole_0(k2_enumset1(X2_42,X3_42,X4_42,X5_42),k1_tarski(X1_42))),k1_tarski(X0_42))),k1_tarski(X6_42))) ),
% 43.37/5.99      inference(superposition,[status(thm)],[c_16,c_33]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_107,plain,
% 43.37/5.99      ( k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) = k5_xboole_0(X2_40,k4_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),X2_40)) ),
% 43.37/5.99      inference(superposition,[status(thm)],[c_16,c_15]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_138,plain,
% 43.37/5.99      ( k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) = k5_xboole_0(X1_40,k4_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X2_40,X0_40)),X1_40)) ),
% 43.37/5.99      inference(superposition,[status(thm)],[c_16,c_107]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_3,negated_conjecture,
% 43.37/5.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(cnf_transformation,[],[f36]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_13,negated_conjecture,
% 43.37/5.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(subtyping,[status(esa)],[c_3]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_36,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(demodulation,[status(thm)],[c_13,c_15]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_37,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(demodulation,[status(thm)],[c_36,c_15]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_287,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK5))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(demodulation,[status(thm)],[c_138,c_37]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_453,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(superposition,[status(thm)],[c_107,c_287]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_44927,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k2_enumset1(sK7,sK1,sK2,sK3),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(demodulation,[status(thm)],[c_549,c_453]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_57781,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k2_enumset1(sK6,sK7,sK1,sK2),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(superposition,[status(thm)],[c_549,c_44927]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_57941,plain,
% 43.37/5.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_enumset1(sK5,sK6,sK7,sK1),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.37/5.99      inference(superposition,[status(thm)],[c_549,c_57781]) ).
% 43.37/5.99  
% 43.37/5.99  cnf(c_57943,plain,
% 43.37/5.99      ( $false ),
% 43.37/5.99      inference(superposition,[status(thm)],[c_549,c_57941]) ).
% 43.37/5.99  
% 43.37/5.99  
% 43.37/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.37/5.99  
% 43.37/5.99  ------                               Statistics
% 43.37/5.99  
% 43.37/5.99  ------ Selected
% 43.37/5.99  
% 43.37/5.99  total_time:                             5.227
% 43.37/5.99  
%------------------------------------------------------------------------------
