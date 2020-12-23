%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:43 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 104 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 129 expanded)
%              Number of equality atoms :   73 ( 128 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f16,f18,f18,f18,f18])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f22,f18])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f23,f18,f30])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f25,f18,f28,f31,f27])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f21,f18,f28])).

fof(f35,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f26,f18,f29,f30,f27])).

cnf(c_18,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_165,plain,
    ( X0_40 != X1_40
    | X0_40 = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
    | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != X1_40 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_282,plain,
    ( X0_40 = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
    | X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_2720,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_17,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_1512,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_290,plain,
    ( X0_40 != X1_40
    | X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != X1_40 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_537,plain,
    ( X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | X0_40 != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_1511,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),k4_xboole_0(X2_40,k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)))) = k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_538,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))),k4_xboole_0(k5_xboole_0(k1_tarski(X2_41),k4_xboole_0(k5_xboole_0(k1_tarski(X3_41),k4_xboole_0(k2_enumset1(X4_41,X5_41,X6_41,X7_41),k1_tarski(X3_41))),k1_tarski(X2_41))),k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))))) = k5_xboole_0(k2_enumset1(X0_41,X1_41,X2_41,X3_41),k4_xboole_0(k2_enumset1(X4_41,X5_41,X6_41,X7_41),k2_enumset1(X0_41,X1_41,X2_41,X3_41))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_163,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_69,plain,
    ( X0_40 != X1_40
    | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != X1_40
    | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = X0_40 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_86,plain,
    ( X0_40 != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
    | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = X0_40
    | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_162,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
    | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_68,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_33,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_13,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2720,c_1512,c_1511,c_538,c_163,c_162,c_68,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:35:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.91/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/0.98  
% 2.91/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/0.98  
% 2.91/0.98  ------  iProver source info
% 2.91/0.98  
% 2.91/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.91/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/0.98  git: non_committed_changes: false
% 2.91/0.98  git: last_make_outside_of_git: false
% 2.91/0.98  
% 2.91/0.98  ------ 
% 2.91/0.98  ------ Parsing...
% 2.91/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.91/0.98  
% 2.91/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.91/0.98  
% 2.91/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.91/0.98  
% 2.91/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.91/0.98  ------ Proving...
% 2.91/0.98  ------ Problem Properties 
% 2.91/0.98  
% 2.91/0.98  
% 2.91/0.98  clauses                                 4
% 2.91/0.98  conjectures                             1
% 2.91/0.98  EPR                                     0
% 2.91/0.98  Horn                                    4
% 2.91/0.98  unary                                   4
% 2.91/0.98  binary                                  0
% 2.91/0.98  lits                                    4
% 2.91/0.98  lits eq                                 4
% 2.91/0.98  fd_pure                                 0
% 2.91/0.98  fd_pseudo                               0
% 2.91/0.98  fd_cond                                 0
% 2.91/0.98  fd_pseudo_cond                          0
% 2.91/0.98  AC symbols                              0
% 2.91/0.98  
% 2.91/0.98  ------ Input Options Time Limit: Unbounded
% 2.91/0.98  
% 2.91/0.98  
% 2.91/0.98  ------ 
% 2.91/0.98  Current options:
% 2.91/0.98  ------ 
% 2.91/0.98  
% 2.91/0.98  
% 2.91/0.98  
% 2.91/0.98  
% 2.91/0.98  ------ Proving...
% 2.91/0.98  
% 2.91/0.98  
% 2.91/0.98  % SZS status Theorem for theBenchmark.p
% 2.91/0.98  
% 2.91/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.91/0.98  
% 2.91/0.98  fof(f1,axiom,(
% 2.91/0.98    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f16,plain,(
% 2.91/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.91/0.98    inference(cnf_transformation,[],[f1])).
% 2.91/0.98  
% 2.91/0.98  fof(f3,axiom,(
% 2.91/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f18,plain,(
% 2.91/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.91/0.98    inference(cnf_transformation,[],[f3])).
% 2.91/0.98  
% 2.91/0.98  fof(f33,plain,(
% 2.91/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 2.91/0.98    inference(definition_unfolding,[],[f16,f18,f18,f18,f18])).
% 2.91/0.98  
% 2.91/0.98  fof(f10,axiom,(
% 2.91/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f25,plain,(
% 2.91/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.91/0.98    inference(cnf_transformation,[],[f10])).
% 2.91/0.98  
% 2.91/0.98  fof(f5,axiom,(
% 2.91/0.98    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f20,plain,(
% 2.91/0.98    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.91/0.98    inference(cnf_transformation,[],[f5])).
% 2.91/0.98  
% 2.91/0.98  fof(f28,plain,(
% 2.91/0.98    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 2.91/0.98    inference(definition_unfolding,[],[f20,f18])).
% 2.91/0.98  
% 2.91/0.98  fof(f8,axiom,(
% 2.91/0.98    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f23,plain,(
% 2.91/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.91/0.98    inference(cnf_transformation,[],[f8])).
% 2.91/0.98  
% 2.91/0.98  fof(f7,axiom,(
% 2.91/0.98    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f22,plain,(
% 2.91/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.91/0.98    inference(cnf_transformation,[],[f7])).
% 2.91/0.98  
% 2.91/0.98  fof(f30,plain,(
% 2.91/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.91/0.98    inference(definition_unfolding,[],[f22,f18])).
% 2.91/0.98  
% 2.91/0.98  fof(f31,plain,(
% 2.91/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.91/0.98    inference(definition_unfolding,[],[f23,f18,f30])).
% 2.91/0.98  
% 2.91/0.98  fof(f4,axiom,(
% 2.91/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f19,plain,(
% 2.91/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.91/0.98    inference(cnf_transformation,[],[f4])).
% 2.91/0.98  
% 2.91/0.98  fof(f27,plain,(
% 2.91/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.91/0.98    inference(definition_unfolding,[],[f19,f18])).
% 2.91/0.98  
% 2.91/0.98  fof(f34,plain,(
% 2.91/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 2.91/0.98    inference(definition_unfolding,[],[f25,f18,f28,f31,f27])).
% 2.91/0.98  
% 2.91/0.98  fof(f11,conjecture,(
% 2.91/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f12,negated_conjecture,(
% 2.91/0.98    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.91/0.98    inference(negated_conjecture,[],[f11])).
% 2.91/0.98  
% 2.91/0.98  fof(f13,plain,(
% 2.91/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.91/0.98    inference(ennf_transformation,[],[f12])).
% 2.91/0.98  
% 2.91/0.98  fof(f14,plain,(
% 2.91/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 2.91/0.98    introduced(choice_axiom,[])).
% 2.91/0.98  
% 2.91/0.98  fof(f15,plain,(
% 2.91/0.98    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 2.91/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).
% 2.91/0.98  
% 2.91/0.98  fof(f26,plain,(
% 2.91/0.98    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 2.91/0.98    inference(cnf_transformation,[],[f15])).
% 2.91/0.98  
% 2.91/0.98  fof(f6,axiom,(
% 2.91/0.98    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 2.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.91/0.98  
% 2.91/0.98  fof(f21,plain,(
% 2.91/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.91/0.98    inference(cnf_transformation,[],[f6])).
% 2.91/0.98  
% 2.91/0.98  fof(f29,plain,(
% 2.91/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 2.91/0.98    inference(definition_unfolding,[],[f21,f18,f28])).
% 2.91/0.98  
% 2.91/0.98  fof(f35,plain,(
% 2.91/0.98    k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 2.91/0.98    inference(definition_unfolding,[],[f26,f18,f29,f30,f27])).
% 2.91/0.98  
% 2.91/0.98  cnf(c_18,plain,
% 2.91/0.98      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 2.91/0.98      theory(equality) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_165,plain,
% 2.91/0.98      ( X0_40 != X1_40
% 2.91/0.98      | X0_40 = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
% 2.91/0.98      | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != X1_40 ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_282,plain,
% 2.91/0.98      ( X0_40 = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
% 2.91/0.98      | X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.91/0.98      | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_165]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_2720,plain,
% 2.91/0.98      ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.91/0.98      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
% 2.91/0.98      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_282]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_17,plain,( X0_40 = X0_40 ),theory(equality) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_1512,plain,
% 2.91/0.98      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_290,plain,
% 2.91/0.98      ( X0_40 != X1_40
% 2.91/0.98      | X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.91/0.98      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != X1_40 ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_537,plain,
% 2.91/0.98      ( X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.91/0.98      | X0_40 != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
% 2.91/0.98      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_290]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_1511,plain,
% 2.91/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
% 2.91/0.98      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.91/0.98      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_537]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_0,plain,
% 2.91/0.98      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 2.91/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_16,plain,
% 2.91/0.98      ( k5_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),k4_xboole_0(X2_40,k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)))) = k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) ),
% 2.91/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_538,plain,
% 2.91/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_2,plain,
% 2.91/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) ),
% 2.91/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_14,plain,
% 2.91/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))),k4_xboole_0(k5_xboole_0(k1_tarski(X2_41),k4_xboole_0(k5_xboole_0(k1_tarski(X3_41),k4_xboole_0(k2_enumset1(X4_41,X5_41,X6_41,X7_41),k1_tarski(X3_41))),k1_tarski(X2_41))),k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))))) = k5_xboole_0(k2_enumset1(X0_41,X1_41,X2_41,X3_41),k4_xboole_0(k2_enumset1(X4_41,X5_41,X6_41,X7_41),k2_enumset1(X0_41,X1_41,X2_41,X3_41))) ),
% 2.91/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_163,plain,
% 2.91/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_69,plain,
% 2.91/0.98      ( X0_40 != X1_40
% 2.91/0.98      | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != X1_40
% 2.91/0.98      | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = X0_40 ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_86,plain,
% 2.91/0.98      ( X0_40 != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
% 2.91/0.98      | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = X0_40
% 2.91/0.98      | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_69]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_162,plain,
% 2.91/0.98      ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3)))
% 2.91/0.98      | k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.91/0.98      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_86]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_68,plain,
% 2.91/0.98      ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) = k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
% 2.91/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_3,negated_conjecture,
% 2.91/0.98      ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
% 2.91/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_13,negated_conjecture,
% 2.91/0.98      ( k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
% 2.91/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(c_33,plain,
% 2.91/0.98      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k2_enumset1(sK0,sK1,sK2,sK3))) ),
% 2.91/0.98      inference(demodulation,[status(thm)],[c_13,c_16]) ).
% 2.91/0.98  
% 2.91/0.98  cnf(contradiction,plain,
% 2.91/0.98      ( $false ),
% 2.91/0.98      inference(minisat,
% 2.91/0.98                [status(thm)],
% 2.91/0.98                [c_2720,c_1512,c_1511,c_538,c_163,c_162,c_68,c_33]) ).
% 2.91/0.98  
% 2.91/0.98  
% 2.91/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.91/0.98  
% 2.91/0.98  ------                               Statistics
% 2.91/0.98  
% 2.91/0.98  ------ Selected
% 2.91/0.98  
% 2.91/0.98  total_time:                             0.203
% 2.91/0.98  
%------------------------------------------------------------------------------
