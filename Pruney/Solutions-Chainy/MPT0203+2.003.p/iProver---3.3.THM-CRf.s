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
% DateTime   : Thu Dec  3 11:28:18 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 112 expanded)
%              Number of clauses        :   48 (  58 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 185 expanded)
%              Number of equality atoms :  137 ( 184 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f15,f16,f16,f16,f16])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f19,f16,f22])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f18,f16,f22])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
   => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f12,f13])).

fof(f24,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f17,f16,f25,f22])).

fof(f31,plain,(
    k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) ),
    inference(definition_unfolding,[],[f24,f16,f27,f26])).

cnf(c_21,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_75,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != X0_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != X0_41 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_27514,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_23,plain,
    ( X0_42 != X1_42
    | X0_41 != X1_41
    | k5_xboole_0(X0_41,X0_42) = k5_xboole_0(X1_41,X1_42) ),
    theory(equality)).

cnf(c_92,plain,
    ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != X0_42
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X0_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(X0_41,X0_42) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_160,plain,
    ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != k4_xboole_0(X0_41,X1_41)
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X2_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(X2_41,k4_xboole_0(X0_41,X1_41)) ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_1185,plain,
    ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != k4_xboole_0(X0_41,X1_41)
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(X0_41,X1_41)) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_8930,plain,
    ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(X0_41,k4_xboole_0(X1_41,X0_41)),k4_xboole_0(X2_41,k5_xboole_0(X0_41,k4_xboole_0(X1_41,X0_41)))) = k5_xboole_0(X0_41,k4_xboole_0(k5_xboole_0(X1_41,k4_xboole_0(X2_41,X1_41)),X0_41)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5009,plain,
    ( k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_70,plain,
    ( X0_41 != X1_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != X1_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = X0_41 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4503,plain,
    ( X0_41 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = X0_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_5008,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))))
    | k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_4503])).

cnf(c_22,plain,
    ( k4_xboole_0(X0_41,X1_41) = k4_xboole_0(X2_41,X3_41)
    | X0_41 != X2_41
    | X1_41 != X3_41 ),
    theory(equality)).

cnf(c_161,plain,
    ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) = k4_xboole_0(X0_41,X1_41)
    | k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) != X0_41
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X1_41 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1188,plain,
    ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) = k4_xboole_0(X0_41,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))
    | k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) != X0_41
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_3499,plain,
    ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) = k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))
    | k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) != k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1188])).

cnf(c_72,plain,
    ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != X0_42
    | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X0_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(X0_41,X0_42) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_97,plain,
    ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != k4_xboole_0(X0_41,X1_41)
    | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X2_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(X2_41,k4_xboole_0(X0_41,X1_41)) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_219,plain,
    ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != k4_xboole_0(X0_41,X1_41)
    | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(X0_41,X1_41)) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_1827,plain,
    ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))
    | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_98,plain,
    ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) = k4_xboole_0(X0_41,X1_41)
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != X0_41
    | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X1_41 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1008,plain,
    ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) = k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),X0_41)
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3)))
    | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X0_41 ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_1217,plain,
    ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) = k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3)))
    | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_19,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1030,plain,
    ( k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) = k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,plain,
    ( k5_xboole_0(k4_enumset1(X0_43,X0_43,X1_43,X2_43,X3_43,X4_43),k4_xboole_0(k1_tarski(X5_43),k4_enumset1(X0_43,X0_43,X1_43,X2_43,X3_43,X4_43))) = k4_enumset1(X0_43,X1_43,X2_43,X3_43,X4_43,X5_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_614,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_223,plain,
    ( X0_41 != X1_41
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X1_41
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = X0_41 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_393,plain,
    ( X0_41 != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = X0_41
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_613,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_17,plain,
    ( k5_xboole_0(k1_tarski(X0_43),k4_xboole_0(k4_enumset1(X1_43,X1_43,X2_43,X3_43,X4_43,X5_43),k1_tarski(X0_43))) = k4_enumset1(X0_43,X1_43,X2_43,X3_43,X4_43,X5_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_426,plain,
    ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_156,plain,
    ( X0_41 != X1_41
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != X1_41
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = X0_41 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_309,plain,
    ( X0_41 != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = X0_41
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_425,plain,
    ( k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
    | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3)))
    | k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_222,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_154,plain,
    ( k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_80,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_69,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_48,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != X0_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != X0_41
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_68,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_4,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27514,c_8930,c_5009,c_5008,c_3499,c_1827,c_1217,c_1030,c_614,c_613,c_426,c_425,c_222,c_154,c_80,c_69,c_68,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:32:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.48/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/1.51  
% 7.48/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.48/1.51  
% 7.48/1.51  ------  iProver source info
% 7.48/1.51  
% 7.48/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.48/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.48/1.51  git: non_committed_changes: false
% 7.48/1.51  git: last_make_outside_of_git: false
% 7.48/1.51  
% 7.48/1.51  ------ 
% 7.48/1.51  ------ Parsing...
% 7.48/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.48/1.51  
% 7.48/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.48/1.51  
% 7.48/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.48/1.51  
% 7.48/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.48/1.51  ------ Proving...
% 7.48/1.51  ------ Problem Properties 
% 7.48/1.51  
% 7.48/1.51  
% 7.48/1.51  clauses                                 5
% 7.48/1.51  conjectures                             1
% 7.48/1.51  EPR                                     0
% 7.48/1.51  Horn                                    5
% 7.48/1.51  unary                                   5
% 7.48/1.51  binary                                  0
% 7.48/1.51  lits                                    5
% 7.48/1.51  lits eq                                 5
% 7.48/1.51  fd_pure                                 0
% 7.48/1.51  fd_pseudo                               0
% 7.48/1.51  fd_cond                                 0
% 7.48/1.51  fd_pseudo_cond                          0
% 7.48/1.51  AC symbols                              0
% 7.48/1.51  
% 7.48/1.51  ------ Input Options Time Limit: Unbounded
% 7.48/1.51  
% 7.48/1.51  
% 7.48/1.51  ------ 
% 7.48/1.51  Current options:
% 7.48/1.51  ------ 
% 7.48/1.51  
% 7.48/1.51  
% 7.48/1.51  
% 7.48/1.51  
% 7.48/1.51  ------ Proving...
% 7.48/1.51  
% 7.48/1.51  
% 7.48/1.51  % SZS status Theorem for theBenchmark.p
% 7.48/1.51  
% 7.48/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.48/1.51  
% 7.48/1.51  fof(f1,axiom,(
% 7.48/1.51    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f15,plain,(
% 7.48/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.48/1.51    inference(cnf_transformation,[],[f1])).
% 7.48/1.51  
% 7.48/1.51  fof(f2,axiom,(
% 7.48/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f16,plain,(
% 7.48/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.48/1.51    inference(cnf_transformation,[],[f2])).
% 7.48/1.51  
% 7.48/1.51  fof(f29,plain,(
% 7.48/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 7.48/1.51    inference(definition_unfolding,[],[f15,f16,f16,f16,f16])).
% 7.48/1.51  
% 7.48/1.51  fof(f5,axiom,(
% 7.48/1.51    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f19,plain,(
% 7.48/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.48/1.51    inference(cnf_transformation,[],[f5])).
% 7.48/1.51  
% 7.48/1.51  fof(f8,axiom,(
% 7.48/1.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f22,plain,(
% 7.48/1.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.48/1.51    inference(cnf_transformation,[],[f8])).
% 7.48/1.51  
% 7.48/1.51  fof(f30,plain,(
% 7.48/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.48/1.51    inference(definition_unfolding,[],[f19,f16,f22])).
% 7.48/1.51  
% 7.48/1.51  fof(f4,axiom,(
% 7.48/1.51    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f18,plain,(
% 7.48/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.48/1.51    inference(cnf_transformation,[],[f4])).
% 7.48/1.51  
% 7.48/1.51  fof(f28,plain,(
% 7.48/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.48/1.51    inference(definition_unfolding,[],[f18,f16,f22])).
% 7.48/1.51  
% 7.48/1.51  fof(f10,conjecture,(
% 7.48/1.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f11,negated_conjecture,(
% 7.48/1.51    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.48/1.51    inference(negated_conjecture,[],[f10])).
% 7.48/1.51  
% 7.48/1.51  fof(f12,plain,(
% 7.48/1.51    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.48/1.51    inference(ennf_transformation,[],[f11])).
% 7.48/1.51  
% 7.48/1.51  fof(f13,plain,(
% 7.48/1.51    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 7.48/1.51    introduced(choice_axiom,[])).
% 7.48/1.51  
% 7.48/1.51  fof(f14,plain,(
% 7.48/1.51    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 7.48/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f12,f13])).
% 7.48/1.51  
% 7.48/1.51  fof(f24,plain,(
% 7.48/1.51    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 7.48/1.51    inference(cnf_transformation,[],[f14])).
% 7.48/1.51  
% 7.48/1.51  fof(f6,axiom,(
% 7.48/1.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f20,plain,(
% 7.48/1.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.48/1.51    inference(cnf_transformation,[],[f6])).
% 7.48/1.51  
% 7.48/1.51  fof(f27,plain,(
% 7.48/1.51    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.48/1.51    inference(definition_unfolding,[],[f20,f25])).
% 7.48/1.51  
% 7.48/1.51  fof(f3,axiom,(
% 7.48/1.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f17,plain,(
% 7.48/1.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.48/1.51    inference(cnf_transformation,[],[f3])).
% 7.48/1.51  
% 7.48/1.51  fof(f7,axiom,(
% 7.48/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.48/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.51  
% 7.48/1.51  fof(f21,plain,(
% 7.48/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.48/1.51    inference(cnf_transformation,[],[f7])).
% 7.48/1.51  
% 7.48/1.51  fof(f25,plain,(
% 7.48/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.48/1.51    inference(definition_unfolding,[],[f21,f22])).
% 7.48/1.51  
% 7.48/1.51  fof(f26,plain,(
% 7.48/1.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.48/1.51    inference(definition_unfolding,[],[f17,f16,f25,f22])).
% 7.48/1.51  
% 7.48/1.51  fof(f31,plain,(
% 7.48/1.51    k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)))),
% 7.48/1.51    inference(definition_unfolding,[],[f24,f16,f27,f26])).
% 7.48/1.51  
% 7.48/1.51  cnf(c_21,plain,
% 7.48/1.51      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 7.48/1.51      theory(equality) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_75,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != X0_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != X0_41 ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_27514,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_75]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_23,plain,
% 7.48/1.51      ( X0_42 != X1_42
% 7.48/1.51      | X0_41 != X1_41
% 7.48/1.51      | k5_xboole_0(X0_41,X0_42) = k5_xboole_0(X1_41,X1_42) ),
% 7.48/1.51      theory(equality) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_92,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != X0_42
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X0_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(X0_41,X0_42) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_160,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != k4_xboole_0(X0_41,X1_41)
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X2_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(X2_41,k4_xboole_0(X0_41,X1_41)) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_92]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_1185,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != k4_xboole_0(X0_41,X1_41)
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(X0_41,X1_41)) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_160]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_8930,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) != k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_1185]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_2,plain,
% 7.48/1.51      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 7.48/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_16,plain,
% 7.48/1.51      ( k5_xboole_0(k5_xboole_0(X0_41,k4_xboole_0(X1_41,X0_41)),k4_xboole_0(X2_41,k5_xboole_0(X0_41,k4_xboole_0(X1_41,X0_41)))) = k5_xboole_0(X0_41,k4_xboole_0(k5_xboole_0(X1_41,k4_xboole_0(X2_41,X1_41)),X0_41)) ),
% 7.48/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_5009,plain,
% 7.48/1.51      ( k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_70,plain,
% 7.48/1.51      ( X0_41 != X1_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != X1_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = X0_41 ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_4503,plain,
% 7.48/1.51      ( X0_41 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = X0_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_70]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_5008,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))))
% 7.48/1.51      | k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_4503]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_22,plain,
% 7.48/1.51      ( k4_xboole_0(X0_41,X1_41) = k4_xboole_0(X2_41,X3_41)
% 7.48/1.51      | X0_41 != X2_41
% 7.48/1.51      | X1_41 != X3_41 ),
% 7.48/1.51      theory(equality) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_161,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) = k4_xboole_0(X0_41,X1_41)
% 7.48/1.51      | k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) != X0_41
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X1_41 ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_1188,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) = k4_xboole_0(X0_41,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))
% 7.48/1.51      | k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) != X0_41
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_161]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_3499,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)) = k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))))
% 7.48/1.51      | k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) != k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_1188]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_72,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != X0_42
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X0_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(X0_41,X0_42) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_97,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != k4_xboole_0(X0_41,X1_41)
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X2_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(X2_41,k4_xboole_0(X0_41,X1_41)) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_72]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_219,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != k4_xboole_0(X0_41,X1_41)
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(X0_41,X1_41)) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_97]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_1827,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) != k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_219]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_98,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) = k4_xboole_0(X0_41,X1_41)
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != X0_41
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X1_41 ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_1008,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) = k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),X0_41)
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3)))
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != X0_41 ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_98]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_1217,plain,
% 7.48/1.51      ( k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)) = k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3)))
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_1008]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_19,plain,( X0_41 = X0_41 ),theory(equality) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_1030,plain,
% 7.48/1.51      ( k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) = k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_3,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 7.48/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_15,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(X0_43,X0_43,X1_43,X2_43,X3_43,X4_43),k4_xboole_0(k1_tarski(X5_43),k4_enumset1(X0_43,X0_43,X1_43,X2_43,X3_43,X4_43))) = k4_enumset1(X0_43,X1_43,X2_43,X3_43,X4_43,X5_43) ),
% 7.48/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_614,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_223,plain,
% 7.48/1.51      ( X0_41 != X1_41
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != X1_41
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = X0_41 ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_393,plain,
% 7.48/1.51      ( X0_41 != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = X0_41
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_223]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_613,plain,
% 7.48/1.51      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 7.48/1.51      | k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK3),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_393]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_1,plain,
% 7.48/1.51      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 7.48/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_17,plain,
% 7.48/1.51      ( k5_xboole_0(k1_tarski(X0_43),k4_xboole_0(k4_enumset1(X1_43,X1_43,X2_43,X3_43,X4_43,X5_43),k1_tarski(X0_43))) = k4_enumset1(X0_43,X1_43,X2_43,X3_43,X4_43,X5_43) ),
% 7.48/1.51      inference(subtyping,[status(esa)],[c_1]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_426,plain,
% 7.48/1.51      ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_156,plain,
% 7.48/1.51      ( X0_41 != X1_41
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != X1_41
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = X0_41 ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_309,plain,
% 7.48/1.51      ( X0_41 != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = X0_41
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_156]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_425,plain,
% 7.48/1.51      ( k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
% 7.48/1.51      | k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3)))
% 7.48/1.51      | k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK3))) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_309]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_222,plain,
% 7.48/1.51      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_154,plain,
% 7.48/1.51      ( k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_80,plain,
% 7.48/1.51      ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_69,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_48,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != X0_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != X0_41
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_68,plain,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)))
% 7.48/1.51      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) ),
% 7.48/1.51      inference(instantiation,[status(thm)],[c_48]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_4,negated_conjecture,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) ),
% 7.48/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(c_14,negated_conjecture,
% 7.48/1.51      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k4_xboole_0(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_xboole_0(k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8),k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3))) ),
% 7.48/1.51      inference(subtyping,[status(esa)],[c_4]) ).
% 7.48/1.51  
% 7.48/1.51  cnf(contradiction,plain,
% 7.48/1.51      ( $false ),
% 7.48/1.51      inference(minisat,
% 7.48/1.51                [status(thm)],
% 7.48/1.51                [c_27514,c_8930,c_5009,c_5008,c_3499,c_1827,c_1217,
% 7.48/1.51                 c_1030,c_614,c_613,c_426,c_425,c_222,c_154,c_80,c_69,
% 7.48/1.51                 c_68,c_14]) ).
% 7.48/1.51  
% 7.48/1.51  
% 7.48/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.48/1.51  
% 7.48/1.51  ------                               Statistics
% 7.48/1.51  
% 7.48/1.51  ------ Selected
% 7.48/1.51  
% 7.48/1.51  total_time:                             0.977
% 7.48/1.51  
%------------------------------------------------------------------------------
