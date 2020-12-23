%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:59 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   73 (1066 expanded)
%              Number of clauses        :   40 ( 359 expanded)
%              Number of leaves         :   12 ( 292 expanded)
%              Depth                    :   22
%              Number of atoms          :   74 (1067 expanded)
%              Number of equality atoms :   73 (1066 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f35,f32])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f35,f32,f36])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f24,f35,f36,f36])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0))))))) ),
    inference(definition_unfolding,[],[f29,f35,f38,f37])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f34,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f34,f36,f38])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_22,plain,
    ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))) = k2_tarski(X0_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_100,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
    inference(superposition,[status(thm)],[c_22,c_23])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))),k5_xboole_0(k2_tarski(X4_35,X5_35),k3_xboole_0(k2_tarski(X4_35,X5_35),k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X5_35),k3_xboole_0(k2_tarski(X4_35,X5_35),k2_tarski(X3_35,X3_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X5_35),k3_xboole_0(k2_tarski(X4_35,X5_35),k2_tarski(X3_35,X3_35)))),k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35))))))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_210,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k2_tarski(X0_35,X0_35)))),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k2_tarski(X0_35,X0_35))))))) = k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))) ),
    inference(superposition,[status(thm)],[c_100,c_20])).

cnf(c_239,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(light_normalisation,[status(thm)],[c_210,c_23])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_21,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_116,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(superposition,[status(thm)],[c_23,c_21])).

cnf(c_245,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(superposition,[status(thm)],[c_116,c_21])).

cnf(c_258,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),k5_xboole_0(X0_34,X1_34))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(superposition,[status(thm)],[c_21,c_245])).

cnf(c_263,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(demodulation,[status(thm)],[c_258,c_116])).

cnf(c_262,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34),X2_34) ),
    inference(superposition,[status(thm)],[c_245,c_21])).

cnf(c_273,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
    inference(light_normalisation,[status(thm)],[c_262,c_263])).

cnf(c_274,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
    inference(demodulation,[status(thm)],[c_273,c_263])).

cnf(c_275,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
    inference(light_normalisation,[status(thm)],[c_274,c_21])).

cnf(c_387,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
    inference(superposition,[status(thm)],[c_21,c_275])).

cnf(c_420,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34)),X3_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))),X3_34) ),
    inference(superposition,[status(thm)],[c_387,c_21])).

cnf(c_429,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34)) ),
    inference(demodulation,[status(thm)],[c_420,c_263,c_275])).

cnf(c_234,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
    inference(superposition,[status(thm)],[c_100,c_21])).

cnf(c_249,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
    inference(superposition,[status(thm)],[c_234,c_21])).

cnf(c_286,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
    inference(light_normalisation,[status(thm)],[c_249,c_249,c_263])).

cnf(c_287,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
    inference(demodulation,[status(thm)],[c_286,c_249,c_263])).

cnf(c_292,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34)),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
    inference(superposition,[status(thm)],[c_287,c_21])).

cnf(c_294,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
    inference(demodulation,[status(thm)],[c_292,c_263])).

cnf(c_295,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
    inference(light_normalisation,[status(thm)],[c_294,c_21])).

cnf(c_511,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34),k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
    inference(superposition,[status(thm)],[c_429,c_295])).

cnf(c_512,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
    inference(demodulation,[status(thm)],[c_511,c_295])).

cnf(c_1083,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(demodulation,[status(thm)],[c_239,c_263,c_512])).

cnf(c_1093,plain,
    ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X2_35,X3_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X2_35,X3_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
    inference(superposition,[status(thm)],[c_22,c_1083])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_36,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_22,c_17])).

cnf(c_39,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_21,c_36])).

cnf(c_41,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_21,c_39])).

cnf(c_1152,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_1093,c_41])).

cnf(c_1184,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_22,c_1152])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:15:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.33/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.04  
% 3.33/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.04  
% 3.33/1.04  ------  iProver source info
% 3.33/1.04  
% 3.33/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.04  git: non_committed_changes: false
% 3.33/1.04  git: last_make_outside_of_git: false
% 3.33/1.04  
% 3.33/1.04  ------ 
% 3.33/1.04  
% 3.33/1.04  ------ Input Options
% 3.33/1.04  
% 3.33/1.04  --out_options                           all
% 3.33/1.04  --tptp_safe_out                         true
% 3.33/1.04  --problem_path                          ""
% 3.33/1.04  --include_path                          ""
% 3.33/1.04  --clausifier                            res/vclausify_rel
% 3.33/1.04  --clausifier_options                    --mode clausify
% 3.33/1.04  --stdin                                 false
% 3.33/1.04  --stats_out                             all
% 3.33/1.04  
% 3.33/1.04  ------ General Options
% 3.33/1.04  
% 3.33/1.04  --fof                                   false
% 3.33/1.04  --time_out_real                         305.
% 3.33/1.04  --time_out_virtual                      -1.
% 3.33/1.04  --symbol_type_check                     false
% 3.33/1.04  --clausify_out                          false
% 3.33/1.04  --sig_cnt_out                           false
% 3.33/1.04  --trig_cnt_out                          false
% 3.33/1.04  --trig_cnt_out_tolerance                1.
% 3.33/1.04  --trig_cnt_out_sk_spl                   false
% 3.33/1.04  --abstr_cl_out                          false
% 3.33/1.04  
% 3.33/1.04  ------ Global Options
% 3.33/1.04  
% 3.33/1.04  --schedule                              default
% 3.33/1.04  --add_important_lit                     false
% 3.33/1.04  --prop_solver_per_cl                    1000
% 3.33/1.04  --min_unsat_core                        false
% 3.33/1.04  --soft_assumptions                      false
% 3.33/1.04  --soft_lemma_size                       3
% 3.33/1.04  --prop_impl_unit_size                   0
% 3.33/1.04  --prop_impl_unit                        []
% 3.33/1.04  --share_sel_clauses                     true
% 3.33/1.04  --reset_solvers                         false
% 3.33/1.04  --bc_imp_inh                            [conj_cone]
% 3.33/1.04  --conj_cone_tolerance                   3.
% 3.33/1.04  --extra_neg_conj                        none
% 3.33/1.04  --large_theory_mode                     true
% 3.33/1.04  --prolific_symb_bound                   200
% 3.33/1.04  --lt_threshold                          2000
% 3.33/1.04  --clause_weak_htbl                      true
% 3.33/1.04  --gc_record_bc_elim                     false
% 3.33/1.04  
% 3.33/1.04  ------ Preprocessing Options
% 3.33/1.04  
% 3.33/1.04  --preprocessing_flag                    true
% 3.33/1.04  --time_out_prep_mult                    0.1
% 3.33/1.04  --splitting_mode                        input
% 3.33/1.04  --splitting_grd                         true
% 3.33/1.04  --splitting_cvd                         false
% 3.33/1.04  --splitting_cvd_svl                     false
% 3.33/1.04  --splitting_nvd                         32
% 3.33/1.04  --sub_typing                            true
% 3.33/1.04  --prep_gs_sim                           true
% 3.33/1.04  --prep_unflatten                        true
% 3.33/1.04  --prep_res_sim                          true
% 3.33/1.04  --prep_upred                            true
% 3.33/1.04  --prep_sem_filter                       exhaustive
% 3.33/1.04  --prep_sem_filter_out                   false
% 3.33/1.04  --pred_elim                             true
% 3.33/1.04  --res_sim_input                         true
% 3.33/1.04  --eq_ax_congr_red                       true
% 3.33/1.04  --pure_diseq_elim                       true
% 3.33/1.04  --brand_transform                       false
% 3.33/1.04  --non_eq_to_eq                          false
% 3.33/1.04  --prep_def_merge                        true
% 3.33/1.04  --prep_def_merge_prop_impl              false
% 3.33/1.04  --prep_def_merge_mbd                    true
% 3.33/1.04  --prep_def_merge_tr_red                 false
% 3.33/1.04  --prep_def_merge_tr_cl                  false
% 3.33/1.04  --smt_preprocessing                     true
% 3.33/1.04  --smt_ac_axioms                         fast
% 3.33/1.04  --preprocessed_out                      false
% 3.33/1.04  --preprocessed_stats                    false
% 3.33/1.04  
% 3.33/1.04  ------ Abstraction refinement Options
% 3.33/1.04  
% 3.33/1.04  --abstr_ref                             []
% 3.33/1.04  --abstr_ref_prep                        false
% 3.33/1.04  --abstr_ref_until_sat                   false
% 3.33/1.04  --abstr_ref_sig_restrict                funpre
% 3.33/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.04  --abstr_ref_under                       []
% 3.33/1.04  
% 3.33/1.04  ------ SAT Options
% 3.33/1.04  
% 3.33/1.04  --sat_mode                              false
% 3.33/1.04  --sat_fm_restart_options                ""
% 3.33/1.04  --sat_gr_def                            false
% 3.33/1.04  --sat_epr_types                         true
% 3.33/1.04  --sat_non_cyclic_types                  false
% 3.33/1.04  --sat_finite_models                     false
% 3.33/1.04  --sat_fm_lemmas                         false
% 3.33/1.04  --sat_fm_prep                           false
% 3.33/1.04  --sat_fm_uc_incr                        true
% 3.33/1.04  --sat_out_model                         small
% 3.33/1.04  --sat_out_clauses                       false
% 3.33/1.04  
% 3.33/1.04  ------ QBF Options
% 3.33/1.04  
% 3.33/1.04  --qbf_mode                              false
% 3.33/1.04  --qbf_elim_univ                         false
% 3.33/1.04  --qbf_dom_inst                          none
% 3.33/1.04  --qbf_dom_pre_inst                      false
% 3.33/1.04  --qbf_sk_in                             false
% 3.33/1.04  --qbf_pred_elim                         true
% 3.33/1.04  --qbf_split                             512
% 3.33/1.04  
% 3.33/1.04  ------ BMC1 Options
% 3.33/1.04  
% 3.33/1.04  --bmc1_incremental                      false
% 3.33/1.04  --bmc1_axioms                           reachable_all
% 3.33/1.04  --bmc1_min_bound                        0
% 3.33/1.04  --bmc1_max_bound                        -1
% 3.33/1.04  --bmc1_max_bound_default                -1
% 3.33/1.04  --bmc1_symbol_reachability              true
% 3.33/1.04  --bmc1_property_lemmas                  false
% 3.33/1.04  --bmc1_k_induction                      false
% 3.33/1.04  --bmc1_non_equiv_states                 false
% 3.33/1.04  --bmc1_deadlock                         false
% 3.33/1.04  --bmc1_ucm                              false
% 3.33/1.04  --bmc1_add_unsat_core                   none
% 3.33/1.04  --bmc1_unsat_core_children              false
% 3.33/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.04  --bmc1_out_stat                         full
% 3.33/1.04  --bmc1_ground_init                      false
% 3.33/1.04  --bmc1_pre_inst_next_state              false
% 3.33/1.04  --bmc1_pre_inst_state                   false
% 3.33/1.04  --bmc1_pre_inst_reach_state             false
% 3.33/1.04  --bmc1_out_unsat_core                   false
% 3.33/1.04  --bmc1_aig_witness_out                  false
% 3.33/1.04  --bmc1_verbose                          false
% 3.33/1.04  --bmc1_dump_clauses_tptp                false
% 3.33/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.04  --bmc1_dump_file                        -
% 3.33/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.04  --bmc1_ucm_extend_mode                  1
% 3.33/1.04  --bmc1_ucm_init_mode                    2
% 3.33/1.04  --bmc1_ucm_cone_mode                    none
% 3.33/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.04  --bmc1_ucm_relax_model                  4
% 3.33/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.04  --bmc1_ucm_layered_model                none
% 3.33/1.04  --bmc1_ucm_max_lemma_size               10
% 3.33/1.04  
% 3.33/1.04  ------ AIG Options
% 3.33/1.04  
% 3.33/1.04  --aig_mode                              false
% 3.33/1.04  
% 3.33/1.04  ------ Instantiation Options
% 3.33/1.04  
% 3.33/1.04  --instantiation_flag                    true
% 3.33/1.04  --inst_sos_flag                         false
% 3.33/1.04  --inst_sos_phase                        true
% 3.33/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.04  --inst_lit_sel_side                     num_symb
% 3.33/1.04  --inst_solver_per_active                1400
% 3.33/1.04  --inst_solver_calls_frac                1.
% 3.33/1.04  --inst_passive_queue_type               priority_queues
% 3.33/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.04  --inst_passive_queues_freq              [25;2]
% 3.33/1.04  --inst_dismatching                      true
% 3.33/1.04  --inst_eager_unprocessed_to_passive     true
% 3.33/1.04  --inst_prop_sim_given                   true
% 3.33/1.04  --inst_prop_sim_new                     false
% 3.33/1.04  --inst_subs_new                         false
% 3.33/1.04  --inst_eq_res_simp                      false
% 3.33/1.04  --inst_subs_given                       false
% 3.33/1.04  --inst_orphan_elimination               true
% 3.33/1.04  --inst_learning_loop_flag               true
% 3.33/1.04  --inst_learning_start                   3000
% 3.33/1.04  --inst_learning_factor                  2
% 3.33/1.04  --inst_start_prop_sim_after_learn       3
% 3.33/1.04  --inst_sel_renew                        solver
% 3.33/1.04  --inst_lit_activity_flag                true
% 3.33/1.04  --inst_restr_to_given                   false
% 3.33/1.04  --inst_activity_threshold               500
% 3.33/1.04  --inst_out_proof                        true
% 3.33/1.04  
% 3.33/1.04  ------ Resolution Options
% 3.33/1.04  
% 3.33/1.04  --resolution_flag                       true
% 3.33/1.04  --res_lit_sel                           adaptive
% 3.33/1.04  --res_lit_sel_side                      none
% 3.33/1.04  --res_ordering                          kbo
% 3.33/1.04  --res_to_prop_solver                    active
% 3.33/1.04  --res_prop_simpl_new                    false
% 3.33/1.04  --res_prop_simpl_given                  true
% 3.33/1.04  --res_passive_queue_type                priority_queues
% 3.33/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.04  --res_passive_queues_freq               [15;5]
% 3.33/1.04  --res_forward_subs                      full
% 3.33/1.04  --res_backward_subs                     full
% 3.33/1.04  --res_forward_subs_resolution           true
% 3.33/1.04  --res_backward_subs_resolution          true
% 3.33/1.04  --res_orphan_elimination                true
% 3.33/1.04  --res_time_limit                        2.
% 3.33/1.04  --res_out_proof                         true
% 3.33/1.04  
% 3.33/1.04  ------ Superposition Options
% 3.33/1.04  
% 3.33/1.04  --superposition_flag                    true
% 3.33/1.04  --sup_passive_queue_type                priority_queues
% 3.33/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.04  --demod_completeness_check              fast
% 3.33/1.04  --demod_use_ground                      true
% 3.33/1.04  --sup_to_prop_solver                    passive
% 3.33/1.04  --sup_prop_simpl_new                    true
% 3.33/1.04  --sup_prop_simpl_given                  true
% 3.33/1.04  --sup_fun_splitting                     false
% 3.33/1.04  --sup_smt_interval                      50000
% 3.33/1.04  
% 3.33/1.04  ------ Superposition Simplification Setup
% 3.33/1.04  
% 3.33/1.04  --sup_indices_passive                   []
% 3.33/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.04  --sup_full_bw                           [BwDemod]
% 3.33/1.04  --sup_immed_triv                        [TrivRules]
% 3.33/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.04  --sup_immed_bw_main                     []
% 3.33/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.04  
% 3.33/1.04  ------ Combination Options
% 3.33/1.04  
% 3.33/1.04  --comb_res_mult                         3
% 3.33/1.04  --comb_sup_mult                         2
% 3.33/1.04  --comb_inst_mult                        10
% 3.33/1.04  
% 3.33/1.04  ------ Debug Options
% 3.33/1.04  
% 3.33/1.04  --dbg_backtrace                         false
% 3.33/1.04  --dbg_dump_prop_clauses                 false
% 3.33/1.04  --dbg_dump_prop_clauses_file            -
% 3.33/1.04  --dbg_out_stat                          false
% 3.33/1.04  ------ Parsing...
% 3.33/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.04  
% 3.33/1.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.33/1.04  
% 3.33/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.04  
% 3.33/1.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.33/1.04  ------ Proving...
% 3.33/1.04  ------ Problem Properties 
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  clauses                                 7
% 3.33/1.04  conjectures                             1
% 3.33/1.04  EPR                                     0
% 3.33/1.04  Horn                                    7
% 3.33/1.04  unary                                   7
% 3.33/1.04  binary                                  0
% 3.33/1.04  lits                                    7
% 3.33/1.04  lits eq                                 7
% 3.33/1.04  fd_pure                                 0
% 3.33/1.04  fd_pseudo                               0
% 3.33/1.04  fd_cond                                 0
% 3.33/1.04  fd_pseudo_cond                          0
% 3.33/1.04  AC symbols                              0
% 3.33/1.04  
% 3.33/1.04  ------ Schedule UEQ
% 3.33/1.04  
% 3.33/1.04  ------ pure equality problem: resolution off 
% 3.33/1.04  
% 3.33/1.04  ------ Option_UEQ Time Limit: Unbounded
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  ------ 
% 3.33/1.04  Current options:
% 3.33/1.04  ------ 
% 3.33/1.04  
% 3.33/1.04  ------ Input Options
% 3.33/1.04  
% 3.33/1.04  --out_options                           all
% 3.33/1.04  --tptp_safe_out                         true
% 3.33/1.04  --problem_path                          ""
% 3.33/1.04  --include_path                          ""
% 3.33/1.04  --clausifier                            res/vclausify_rel
% 3.33/1.04  --clausifier_options                    --mode clausify
% 3.33/1.04  --stdin                                 false
% 3.33/1.04  --stats_out                             all
% 3.33/1.04  
% 3.33/1.04  ------ General Options
% 3.33/1.04  
% 3.33/1.04  --fof                                   false
% 3.33/1.04  --time_out_real                         305.
% 3.33/1.04  --time_out_virtual                      -1.
% 3.33/1.04  --symbol_type_check                     false
% 3.33/1.04  --clausify_out                          false
% 3.33/1.04  --sig_cnt_out                           false
% 3.33/1.04  --trig_cnt_out                          false
% 3.33/1.04  --trig_cnt_out_tolerance                1.
% 3.33/1.04  --trig_cnt_out_sk_spl                   false
% 3.33/1.04  --abstr_cl_out                          false
% 3.33/1.04  
% 3.33/1.04  ------ Global Options
% 3.33/1.04  
% 3.33/1.04  --schedule                              default
% 3.33/1.04  --add_important_lit                     false
% 3.33/1.04  --prop_solver_per_cl                    1000
% 3.33/1.04  --min_unsat_core                        false
% 3.33/1.04  --soft_assumptions                      false
% 3.33/1.04  --soft_lemma_size                       3
% 3.33/1.04  --prop_impl_unit_size                   0
% 3.33/1.04  --prop_impl_unit                        []
% 3.33/1.04  --share_sel_clauses                     true
% 3.33/1.04  --reset_solvers                         false
% 3.33/1.04  --bc_imp_inh                            [conj_cone]
% 3.33/1.04  --conj_cone_tolerance                   3.
% 3.33/1.04  --extra_neg_conj                        none
% 3.33/1.04  --large_theory_mode                     true
% 3.33/1.04  --prolific_symb_bound                   200
% 3.33/1.04  --lt_threshold                          2000
% 3.33/1.04  --clause_weak_htbl                      true
% 3.33/1.04  --gc_record_bc_elim                     false
% 3.33/1.04  
% 3.33/1.04  ------ Preprocessing Options
% 3.33/1.04  
% 3.33/1.04  --preprocessing_flag                    true
% 3.33/1.04  --time_out_prep_mult                    0.1
% 3.33/1.04  --splitting_mode                        input
% 3.33/1.04  --splitting_grd                         true
% 3.33/1.04  --splitting_cvd                         false
% 3.33/1.04  --splitting_cvd_svl                     false
% 3.33/1.04  --splitting_nvd                         32
% 3.33/1.04  --sub_typing                            true
% 3.33/1.04  --prep_gs_sim                           true
% 3.33/1.04  --prep_unflatten                        true
% 3.33/1.04  --prep_res_sim                          true
% 3.33/1.04  --prep_upred                            true
% 3.33/1.04  --prep_sem_filter                       exhaustive
% 3.33/1.04  --prep_sem_filter_out                   false
% 3.33/1.04  --pred_elim                             true
% 3.33/1.04  --res_sim_input                         true
% 3.33/1.04  --eq_ax_congr_red                       true
% 3.33/1.04  --pure_diseq_elim                       true
% 3.33/1.04  --brand_transform                       false
% 3.33/1.04  --non_eq_to_eq                          false
% 3.33/1.04  --prep_def_merge                        true
% 3.33/1.04  --prep_def_merge_prop_impl              false
% 3.33/1.04  --prep_def_merge_mbd                    true
% 3.33/1.04  --prep_def_merge_tr_red                 false
% 3.33/1.04  --prep_def_merge_tr_cl                  false
% 3.33/1.04  --smt_preprocessing                     true
% 3.33/1.04  --smt_ac_axioms                         fast
% 3.33/1.04  --preprocessed_out                      false
% 3.33/1.04  --preprocessed_stats                    false
% 3.33/1.04  
% 3.33/1.04  ------ Abstraction refinement Options
% 3.33/1.04  
% 3.33/1.04  --abstr_ref                             []
% 3.33/1.04  --abstr_ref_prep                        false
% 3.33/1.04  --abstr_ref_until_sat                   false
% 3.33/1.04  --abstr_ref_sig_restrict                funpre
% 3.33/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.04  --abstr_ref_under                       []
% 3.33/1.04  
% 3.33/1.04  ------ SAT Options
% 3.33/1.04  
% 3.33/1.04  --sat_mode                              false
% 3.33/1.04  --sat_fm_restart_options                ""
% 3.33/1.04  --sat_gr_def                            false
% 3.33/1.04  --sat_epr_types                         true
% 3.33/1.04  --sat_non_cyclic_types                  false
% 3.33/1.04  --sat_finite_models                     false
% 3.33/1.04  --sat_fm_lemmas                         false
% 3.33/1.04  --sat_fm_prep                           false
% 3.33/1.04  --sat_fm_uc_incr                        true
% 3.33/1.04  --sat_out_model                         small
% 3.33/1.04  --sat_out_clauses                       false
% 3.33/1.04  
% 3.33/1.04  ------ QBF Options
% 3.33/1.04  
% 3.33/1.04  --qbf_mode                              false
% 3.33/1.04  --qbf_elim_univ                         false
% 3.33/1.04  --qbf_dom_inst                          none
% 3.33/1.04  --qbf_dom_pre_inst                      false
% 3.33/1.04  --qbf_sk_in                             false
% 3.33/1.04  --qbf_pred_elim                         true
% 3.33/1.04  --qbf_split                             512
% 3.33/1.04  
% 3.33/1.04  ------ BMC1 Options
% 3.33/1.04  
% 3.33/1.04  --bmc1_incremental                      false
% 3.33/1.04  --bmc1_axioms                           reachable_all
% 3.33/1.04  --bmc1_min_bound                        0
% 3.33/1.04  --bmc1_max_bound                        -1
% 3.33/1.04  --bmc1_max_bound_default                -1
% 3.33/1.04  --bmc1_symbol_reachability              true
% 3.33/1.04  --bmc1_property_lemmas                  false
% 3.33/1.04  --bmc1_k_induction                      false
% 3.33/1.04  --bmc1_non_equiv_states                 false
% 3.33/1.04  --bmc1_deadlock                         false
% 3.33/1.04  --bmc1_ucm                              false
% 3.33/1.04  --bmc1_add_unsat_core                   none
% 3.33/1.04  --bmc1_unsat_core_children              false
% 3.33/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.04  --bmc1_out_stat                         full
% 3.33/1.04  --bmc1_ground_init                      false
% 3.33/1.04  --bmc1_pre_inst_next_state              false
% 3.33/1.04  --bmc1_pre_inst_state                   false
% 3.33/1.04  --bmc1_pre_inst_reach_state             false
% 3.33/1.04  --bmc1_out_unsat_core                   false
% 3.33/1.04  --bmc1_aig_witness_out                  false
% 3.33/1.04  --bmc1_verbose                          false
% 3.33/1.04  --bmc1_dump_clauses_tptp                false
% 3.33/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.04  --bmc1_dump_file                        -
% 3.33/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.04  --bmc1_ucm_extend_mode                  1
% 3.33/1.04  --bmc1_ucm_init_mode                    2
% 3.33/1.04  --bmc1_ucm_cone_mode                    none
% 3.33/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.04  --bmc1_ucm_relax_model                  4
% 3.33/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.04  --bmc1_ucm_layered_model                none
% 3.33/1.04  --bmc1_ucm_max_lemma_size               10
% 3.33/1.04  
% 3.33/1.04  ------ AIG Options
% 3.33/1.04  
% 3.33/1.04  --aig_mode                              false
% 3.33/1.04  
% 3.33/1.04  ------ Instantiation Options
% 3.33/1.04  
% 3.33/1.04  --instantiation_flag                    false
% 3.33/1.04  --inst_sos_flag                         false
% 3.33/1.04  --inst_sos_phase                        true
% 3.33/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.04  --inst_lit_sel_side                     num_symb
% 3.33/1.04  --inst_solver_per_active                1400
% 3.33/1.04  --inst_solver_calls_frac                1.
% 3.33/1.04  --inst_passive_queue_type               priority_queues
% 3.33/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.04  --inst_passive_queues_freq              [25;2]
% 3.33/1.04  --inst_dismatching                      true
% 3.33/1.04  --inst_eager_unprocessed_to_passive     true
% 3.33/1.04  --inst_prop_sim_given                   true
% 3.33/1.04  --inst_prop_sim_new                     false
% 3.33/1.04  --inst_subs_new                         false
% 3.33/1.04  --inst_eq_res_simp                      false
% 3.33/1.04  --inst_subs_given                       false
% 3.33/1.04  --inst_orphan_elimination               true
% 3.33/1.04  --inst_learning_loop_flag               true
% 3.33/1.04  --inst_learning_start                   3000
% 3.33/1.04  --inst_learning_factor                  2
% 3.33/1.04  --inst_start_prop_sim_after_learn       3
% 3.33/1.04  --inst_sel_renew                        solver
% 3.33/1.04  --inst_lit_activity_flag                true
% 3.33/1.04  --inst_restr_to_given                   false
% 3.33/1.04  --inst_activity_threshold               500
% 3.33/1.04  --inst_out_proof                        true
% 3.33/1.04  
% 3.33/1.04  ------ Resolution Options
% 3.33/1.04  
% 3.33/1.04  --resolution_flag                       false
% 3.33/1.04  --res_lit_sel                           adaptive
% 3.33/1.04  --res_lit_sel_side                      none
% 3.33/1.04  --res_ordering                          kbo
% 3.33/1.04  --res_to_prop_solver                    active
% 3.33/1.04  --res_prop_simpl_new                    false
% 3.33/1.04  --res_prop_simpl_given                  true
% 3.33/1.04  --res_passive_queue_type                priority_queues
% 3.33/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.04  --res_passive_queues_freq               [15;5]
% 3.33/1.04  --res_forward_subs                      full
% 3.33/1.04  --res_backward_subs                     full
% 3.33/1.04  --res_forward_subs_resolution           true
% 3.33/1.04  --res_backward_subs_resolution          true
% 3.33/1.04  --res_orphan_elimination                true
% 3.33/1.04  --res_time_limit                        2.
% 3.33/1.04  --res_out_proof                         true
% 3.33/1.04  
% 3.33/1.04  ------ Superposition Options
% 3.33/1.04  
% 3.33/1.04  --superposition_flag                    true
% 3.33/1.04  --sup_passive_queue_type                priority_queues
% 3.33/1.04  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.04  --demod_completeness_check              fast
% 3.33/1.04  --demod_use_ground                      true
% 3.33/1.04  --sup_to_prop_solver                    active
% 3.33/1.04  --sup_prop_simpl_new                    false
% 3.33/1.04  --sup_prop_simpl_given                  false
% 3.33/1.04  --sup_fun_splitting                     true
% 3.33/1.04  --sup_smt_interval                      10000
% 3.33/1.04  
% 3.33/1.04  ------ Superposition Simplification Setup
% 3.33/1.04  
% 3.33/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.33/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.33/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.04  --sup_full_triv                         [TrivRules]
% 3.33/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.33/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.33/1.04  --sup_immed_triv                        [TrivRules]
% 3.33/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.04  --sup_immed_bw_main                     []
% 3.33/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.33/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.04  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.33/1.04  
% 3.33/1.04  ------ Combination Options
% 3.33/1.04  
% 3.33/1.04  --comb_res_mult                         1
% 3.33/1.04  --comb_sup_mult                         1
% 3.33/1.04  --comb_inst_mult                        1000000
% 3.33/1.04  
% 3.33/1.04  ------ Debug Options
% 3.33/1.04  
% 3.33/1.04  --dbg_backtrace                         false
% 3.33/1.04  --dbg_dump_prop_clauses                 false
% 3.33/1.04  --dbg_dump_prop_clauses_file            -
% 3.33/1.04  --dbg_out_stat                          false
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  ------ Proving...
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  % SZS status Theorem for theBenchmark.p
% 3.33/1.04  
% 3.33/1.04   Resolution empty clause
% 3.33/1.04  
% 3.33/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.04  
% 3.33/1.04  fof(f1,axiom,(
% 3.33/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f20,plain,(
% 3.33/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f1])).
% 3.33/1.04  
% 3.33/1.04  fof(f14,axiom,(
% 3.33/1.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f33,plain,(
% 3.33/1.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f14])).
% 3.33/1.04  
% 3.33/1.04  fof(f7,axiom,(
% 3.33/1.04    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f26,plain,(
% 3.33/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f7])).
% 3.33/1.04  
% 3.33/1.04  fof(f4,axiom,(
% 3.33/1.04    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f23,plain,(
% 3.33/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f4])).
% 3.33/1.04  
% 3.33/1.04  fof(f2,axiom,(
% 3.33/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f21,plain,(
% 3.33/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.33/1.04    inference(cnf_transformation,[],[f2])).
% 3.33/1.04  
% 3.33/1.04  fof(f35,plain,(
% 3.33/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.33/1.04    inference(definition_unfolding,[],[f23,f21])).
% 3.33/1.04  
% 3.33/1.04  fof(f13,axiom,(
% 3.33/1.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f32,plain,(
% 3.33/1.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f13])).
% 3.33/1.04  
% 3.33/1.04  fof(f36,plain,(
% 3.33/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 3.33/1.04    inference(definition_unfolding,[],[f26,f35,f32])).
% 3.33/1.04  
% 3.33/1.04  fof(f41,plain,(
% 3.33/1.04    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 3.33/1.04    inference(definition_unfolding,[],[f33,f36])).
% 3.33/1.04  
% 3.33/1.04  fof(f10,axiom,(
% 3.33/1.04    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f29,plain,(
% 3.33/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f10])).
% 3.33/1.04  
% 3.33/1.04  fof(f8,axiom,(
% 3.33/1.04    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f27,plain,(
% 3.33/1.04    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f8])).
% 3.33/1.04  
% 3.33/1.04  fof(f38,plain,(
% 3.33/1.04    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.33/1.04    inference(definition_unfolding,[],[f27,f35,f32,f36])).
% 3.33/1.04  
% 3.33/1.04  fof(f5,axiom,(
% 3.33/1.04    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f24,plain,(
% 3.33/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f5])).
% 3.33/1.04  
% 3.33/1.04  fof(f37,plain,(
% 3.33/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.33/1.04    inference(definition_unfolding,[],[f24,f35,f36,f36])).
% 3.33/1.04  
% 3.33/1.04  fof(f42,plain,(
% 3.33/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))))))) )),
% 3.33/1.04    inference(definition_unfolding,[],[f29,f35,f38,f37])).
% 3.33/1.04  
% 3.33/1.04  fof(f3,axiom,(
% 3.33/1.04    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f22,plain,(
% 3.33/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.33/1.04    inference(cnf_transformation,[],[f3])).
% 3.33/1.04  
% 3.33/1.04  fof(f15,conjecture,(
% 3.33/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.33/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.04  
% 3.33/1.04  fof(f16,negated_conjecture,(
% 3.33/1.04    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.33/1.04    inference(negated_conjecture,[],[f15])).
% 3.33/1.04  
% 3.33/1.04  fof(f17,plain,(
% 3.33/1.04    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 3.33/1.04    inference(ennf_transformation,[],[f16])).
% 3.33/1.04  
% 3.33/1.04  fof(f18,plain,(
% 3.33/1.04    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 3.33/1.04    introduced(choice_axiom,[])).
% 3.33/1.04  
% 3.33/1.04  fof(f19,plain,(
% 3.33/1.04    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 3.33/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 3.33/1.04  
% 3.33/1.04  fof(f34,plain,(
% 3.33/1.04    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 3.33/1.04    inference(cnf_transformation,[],[f19])).
% 3.33/1.04  
% 3.33/1.04  fof(f45,plain,(
% 3.33/1.04    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0))))),
% 3.33/1.04    inference(definition_unfolding,[],[f34,f36,f38])).
% 3.33/1.04  
% 3.33/1.04  cnf(c_1,plain,
% 3.33/1.04      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.33/1.04      inference(cnf_transformation,[],[f20]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_22,plain,
% 3.33/1.04      ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
% 3.33/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_0,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 3.33/1.04      inference(cnf_transformation,[],[f41]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_23,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))) = k2_tarski(X0_35,X1_35) ),
% 3.33/1.04      inference(subtyping,[status(esa)],[c_0]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_100,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)))) = k2_tarski(X0_35,X1_35) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_22,c_23]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_3,plain,
% 3.33/1.04      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k2_tarski(X3,X3)))),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) ),
% 3.33/1.04      inference(cnf_transformation,[],[f42]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_20,plain,
% 3.33/1.04      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))),k5_xboole_0(k2_tarski(X4_35,X5_35),k3_xboole_0(k2_tarski(X4_35,X5_35),k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35))))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35)))),k5_xboole_0(k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X5_35),k3_xboole_0(k2_tarski(X4_35,X5_35),k2_tarski(X3_35,X3_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X3_35,X3_35),k5_xboole_0(k2_tarski(X4_35,X5_35),k3_xboole_0(k2_tarski(X4_35,X5_35),k2_tarski(X3_35,X3_35)))),k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X2_35),k3_xboole_0(k2_tarski(X1_35,X2_35),k2_tarski(X0_35,X0_35))))))) ),
% 3.33/1.04      inference(subtyping,[status(esa)],[c_3]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_210,plain,
% 3.33/1.04      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k2_tarski(X0_35,X0_35)))),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)))),k2_tarski(X0_35,X0_35))))))) = k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_100,c_20]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_239,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 3.33/1.04      inference(light_normalisation,[status(thm)],[c_210,c_23]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_2,plain,
% 3.33/1.04      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.33/1.04      inference(cnf_transformation,[],[f22]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_21,plain,
% 3.33/1.04      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
% 3.33/1.04      inference(subtyping,[status(esa)],[c_2]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_116,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_23,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_245,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_116,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_258,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),k5_xboole_0(X0_34,X1_34))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_21,c_245]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_263,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_258,c_116]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_262,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34),X2_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_245,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_273,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35))),X0_34),X1_34),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
% 3.33/1.04      inference(light_normalisation,[status(thm)],[c_262,c_263]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_274,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_273,c_263]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_275,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
% 3.33/1.04      inference(light_normalisation,[status(thm)],[c_274,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_387,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_21,c_275]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_420,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X1_35),k2_tarski(X0_35,X0_35)),k5_xboole_0(X0_34,X1_34)),X2_34)),X3_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))),X3_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_387,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_429,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),k5_xboole_0(X2_34,X3_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)),X3_34)) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_420,c_263,c_275]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_234,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35))),X0_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_100,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_249,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),X0_34),X1_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_234,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_286,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35))),X0_34),X1_34)) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
% 3.33/1.04      inference(light_normalisation,[status(thm)],[c_249,c_249,c_263]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_287,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_286,c_249,c_263]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_292,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34)),X2_34)) = k5_xboole_0(k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,X1_34)),X2_34) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_287,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_294,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34)) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_292,c_263]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_295,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34),X2_34))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34))) ),
% 3.33/1.04      inference(light_normalisation,[status(thm)],[c_294,c_21]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_511,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k2_tarski(X0_35,X0_35),k2_tarski(X0_35,X1_35)),X0_34),X1_34),k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_429,c_295]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_512,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(X1_34,k5_xboole_0(X2_34,X3_34)))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(X0_34,k5_xboole_0(k5_xboole_0(X1_34,X2_34),X3_34))) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_511,c_295]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_1083,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X1_35,X1_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_239,c_263,c_512]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_1093,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(X0_35,X0_35),k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k5_xboole_0(k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X2_35,X3_35)),k3_xboole_0(k5_xboole_0(k2_tarski(X1_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X1_35,X1_35),k2_tarski(X2_35,X3_35)))),k2_tarski(X0_35,X0_35)))))) = k5_xboole_0(k2_tarski(X0_35,X1_35),k5_xboole_0(k2_tarski(X2_35,X3_35),k3_xboole_0(k2_tarski(X2_35,X3_35),k2_tarski(X0_35,X1_35)))) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_22,c_1083]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_6,negated_conjecture,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
% 3.33/1.04      inference(cnf_transformation,[],[f45]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_17,negated_conjecture,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
% 3.33/1.04      inference(subtyping,[status(esa)],[c_6]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_36,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_22,c_17]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_39,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_21,c_36]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_41,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k2_tarski(sK0,sK0)))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_21,c_39]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_1152,plain,
% 3.33/1.04      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) ),
% 3.33/1.04      inference(demodulation,[status(thm)],[c_1093,c_41]) ).
% 3.33/1.04  
% 3.33/1.04  cnf(c_1184,plain,
% 3.33/1.04      ( $false ),
% 3.33/1.04      inference(superposition,[status(thm)],[c_22,c_1152]) ).
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.04  
% 3.33/1.04  ------                               Statistics
% 3.33/1.04  
% 3.33/1.04  ------ General
% 3.33/1.04  
% 3.33/1.04  abstr_ref_over_cycles:                  0
% 3.33/1.04  abstr_ref_under_cycles:                 0
% 3.33/1.04  gc_basic_clause_elim:                   0
% 3.33/1.04  forced_gc_time:                         0
% 3.33/1.04  parsing_time:                           0.007
% 3.33/1.04  unif_index_cands_time:                  0.
% 3.33/1.04  unif_index_add_time:                    0.
% 3.33/1.04  orderings_time:                         0.
% 3.33/1.04  out_proof_time:                         0.01
% 3.33/1.04  total_time:                             0.129
% 3.33/1.04  num_of_symbols:                         39
% 3.33/1.04  num_of_terms:                           4626
% 3.33/1.04  
% 3.33/1.04  ------ Preprocessing
% 3.33/1.04  
% 3.33/1.04  num_of_splits:                          0
% 3.33/1.04  num_of_split_atoms:                     0
% 3.33/1.04  num_of_reused_defs:                     0
% 3.33/1.04  num_eq_ax_congr_red:                    2
% 3.33/1.04  num_of_sem_filtered_clauses:            0
% 3.33/1.04  num_of_subtypes:                        2
% 3.33/1.04  monotx_restored_types:                  0
% 3.33/1.04  sat_num_of_epr_types:                   0
% 3.33/1.04  sat_num_of_non_cyclic_types:            0
% 3.33/1.04  sat_guarded_non_collapsed_types:        0
% 3.33/1.04  num_pure_diseq_elim:                    0
% 3.33/1.04  simp_replaced_by:                       0
% 3.33/1.04  res_preprocessed:                       18
% 3.33/1.04  prep_upred:                             0
% 3.33/1.04  prep_unflattend:                        0
% 3.33/1.04  smt_new_axioms:                         0
% 3.33/1.04  pred_elim_cands:                        0
% 3.33/1.04  pred_elim:                              0
% 3.33/1.04  pred_elim_cl:                           0
% 3.33/1.04  pred_elim_cycles:                       0
% 3.33/1.04  merged_defs:                            0
% 3.33/1.04  merged_defs_ncl:                        0
% 3.33/1.04  bin_hyper_res:                          0
% 3.33/1.04  prep_cycles:                            2
% 3.33/1.04  pred_elim_time:                         0.
% 3.33/1.04  splitting_time:                         0.
% 3.33/1.04  sem_filter_time:                        0.
% 3.33/1.04  monotx_time:                            0.
% 3.33/1.04  subtype_inf_time:                       0.
% 3.33/1.04  
% 3.33/1.04  ------ Problem properties
% 3.33/1.04  
% 3.33/1.04  clauses:                                7
% 3.33/1.04  conjectures:                            1
% 3.33/1.04  epr:                                    0
% 3.33/1.04  horn:                                   7
% 3.33/1.04  ground:                                 1
% 3.33/1.04  unary:                                  7
% 3.33/1.04  binary:                                 0
% 3.33/1.04  lits:                                   7
% 3.33/1.04  lits_eq:                                7
% 3.33/1.04  fd_pure:                                0
% 3.33/1.04  fd_pseudo:                              0
% 3.33/1.04  fd_cond:                                0
% 3.33/1.04  fd_pseudo_cond:                         0
% 3.33/1.04  ac_symbols:                             0
% 3.33/1.04  
% 3.33/1.04  ------ Propositional Solver
% 3.33/1.04  
% 3.33/1.04  prop_solver_calls:                      13
% 3.33/1.04  prop_fast_solver_calls:                 48
% 3.33/1.04  smt_solver_calls:                       0
% 3.33/1.04  smt_fast_solver_calls:                  0
% 3.33/1.04  prop_num_of_clauses:                    78
% 3.33/1.04  prop_preprocess_simplified:             239
% 3.33/1.04  prop_fo_subsumed:                       0
% 3.33/1.04  prop_solver_time:                       0.
% 3.33/1.04  smt_solver_time:                        0.
% 3.33/1.04  smt_fast_solver_time:                   0.
% 3.33/1.04  prop_fast_solver_time:                  0.
% 3.33/1.04  prop_unsat_core_time:                   0.
% 3.33/1.04  
% 3.33/1.04  ------ QBF
% 3.33/1.04  
% 3.33/1.04  qbf_q_res:                              0
% 3.33/1.04  qbf_num_tautologies:                    0
% 3.33/1.04  qbf_prep_cycles:                        0
% 3.33/1.04  
% 3.33/1.04  ------ BMC1
% 3.33/1.04  
% 3.33/1.04  bmc1_current_bound:                     -1
% 3.33/1.04  bmc1_last_solved_bound:                 -1
% 3.33/1.04  bmc1_unsat_core_size:                   -1
% 3.33/1.04  bmc1_unsat_core_parents_size:           -1
% 3.33/1.04  bmc1_merge_next_fun:                    0
% 3.33/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.04  
% 3.33/1.04  ------ Instantiation
% 3.33/1.04  
% 3.33/1.04  inst_num_of_clauses:                    0
% 3.33/1.04  inst_num_in_passive:                    0
% 3.33/1.04  inst_num_in_active:                     0
% 3.33/1.04  inst_num_in_unprocessed:                0
% 3.33/1.04  inst_num_of_loops:                      0
% 3.33/1.04  inst_num_of_learning_restarts:          0
% 3.33/1.04  inst_num_moves_active_passive:          0
% 3.33/1.04  inst_lit_activity:                      0
% 3.33/1.04  inst_lit_activity_moves:                0
% 3.33/1.04  inst_num_tautologies:                   0
% 3.33/1.04  inst_num_prop_implied:                  0
% 3.33/1.04  inst_num_existing_simplified:           0
% 3.33/1.04  inst_num_eq_res_simplified:             0
% 3.33/1.04  inst_num_child_elim:                    0
% 3.33/1.04  inst_num_of_dismatching_blockings:      0
% 3.33/1.04  inst_num_of_non_proper_insts:           0
% 3.33/1.04  inst_num_of_duplicates:                 0
% 3.33/1.04  inst_inst_num_from_inst_to_res:         0
% 3.33/1.04  inst_dismatching_checking_time:         0.
% 3.33/1.04  
% 3.33/1.04  ------ Resolution
% 3.33/1.04  
% 3.33/1.04  res_num_of_clauses:                     0
% 3.33/1.04  res_num_in_passive:                     0
% 3.33/1.04  res_num_in_active:                      0
% 3.33/1.04  res_num_of_loops:                       20
% 3.33/1.04  res_forward_subset_subsumed:            0
% 3.33/1.04  res_backward_subset_subsumed:           0
% 3.33/1.04  res_forward_subsumed:                   0
% 3.33/1.04  res_backward_subsumed:                  0
% 3.33/1.04  res_forward_subsumption_resolution:     0
% 3.33/1.04  res_backward_subsumption_resolution:    0
% 3.33/1.04  res_clause_to_clause_subsumption:       1296
% 3.33/1.04  res_orphan_elimination:                 0
% 3.33/1.04  res_tautology_del:                      0
% 3.33/1.04  res_num_eq_res_simplified:              0
% 3.33/1.04  res_num_sel_changes:                    0
% 3.33/1.04  res_moves_from_active_to_pass:          0
% 3.33/1.04  
% 3.33/1.04  ------ Superposition
% 3.33/1.04  
% 3.33/1.04  sup_time_total:                         0.
% 3.33/1.04  sup_time_generating:                    0.
% 3.33/1.04  sup_time_sim_full:                      0.
% 3.33/1.04  sup_time_sim_immed:                     0.
% 3.33/1.04  
% 3.33/1.04  sup_num_of_clauses:                     144
% 3.33/1.04  sup_num_in_active:                      22
% 3.33/1.04  sup_num_in_passive:                     122
% 3.33/1.04  sup_num_of_loops:                       36
% 3.33/1.04  sup_fw_superposition:                   411
% 3.33/1.04  sup_bw_superposition:                   186
% 3.33/1.04  sup_immediate_simplified:               345
% 3.33/1.04  sup_given_eliminated:                   2
% 3.33/1.04  comparisons_done:                       0
% 3.33/1.04  comparisons_avoided:                    0
% 3.33/1.04  
% 3.33/1.04  ------ Simplifications
% 3.33/1.04  
% 3.33/1.04  
% 3.33/1.04  sim_fw_subset_subsumed:                 0
% 3.33/1.04  sim_bw_subset_subsumed:                 0
% 3.33/1.04  sim_fw_subsumed:                        21
% 3.33/1.04  sim_bw_subsumed:                        1
% 3.33/1.04  sim_fw_subsumption_res:                 0
% 3.33/1.04  sim_bw_subsumption_res:                 0
% 3.33/1.04  sim_tautology_del:                      0
% 3.33/1.04  sim_eq_tautology_del:                   124
% 3.33/1.04  sim_eq_res_simp:                        0
% 3.33/1.04  sim_fw_demodulated:                     460
% 3.33/1.04  sim_bw_demodulated:                     19
% 3.33/1.04  sim_light_normalised:                   55
% 3.33/1.04  sim_joinable_taut:                      0
% 3.33/1.04  sim_joinable_simp:                      0
% 3.33/1.04  sim_ac_normalised:                      0
% 3.33/1.04  sim_smt_subsumption:                    0
% 3.33/1.04  
%------------------------------------------------------------------------------
