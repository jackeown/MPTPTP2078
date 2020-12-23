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
% DateTime   : Thu Dec  3 11:28:18 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 129 expanded)
%              Number of clauses        :   34 (  42 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 174 expanded)
%              Number of equality atoms :  106 ( 173 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f33,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f33])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f21,f34])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f18,f29,f30])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f19,f34,f35,f31])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f20,f25,f34])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
   => k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f15])).

fof(f28,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(definition_unfolding,[],[f28,f33,f31])).

cnf(c_16,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_69,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != X0_39
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != X0_39 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1284,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_13,plain,
    ( k2_xboole_0(k2_xboole_0(X0_39,X1_39),X2_39) = k2_xboole_0(X0_39,k2_xboole_0(X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_758,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_84,plain,
    ( k2_xboole_0(X0_39,X1_39) != X2_39
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != X2_39
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_39,X1_39) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_365,plain,
    ( k2_xboole_0(X0_39,X1_39) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_39,X1_39)
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_757,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_17,plain,
    ( X0_39 != X1_39
    | X2_39 != X3_39
    | k2_xboole_0(X0_39,X2_39) = k2_xboole_0(X1_39,X3_39) ),
    theory(equality)).

cnf(c_46,plain,
    ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) != X0_39
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != X1_39
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X1_39,X0_39) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_354,plain,
    ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) != X0_39
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0_39) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_742,plain,
    ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_2,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( k2_xboole_0(k5_enumset1(X0_40,X0_40,X0_40,X0_40,X0_40,X0_40,X0_40),k2_xboole_0(k5_enumset1(X1_40,X1_40,X1_40,X1_40,X1_40,X1_40,X1_40),k5_enumset1(X2_40,X3_40,X4_40,X5_40,X6_40,X7_40,X8_40))) = k2_xboole_0(k5_enumset1(X0_40,X0_40,X0_40,X0_40,X1_40,X2_40,X3_40),k5_enumset1(X4_40,X4_40,X4_40,X5_40,X6_40,X7_40,X8_40)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_282,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_149,plain,
    ( k2_xboole_0(X0_39,X1_39) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_39,X1_39)
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_281,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_15,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_277,plain,
    ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,plain,
    ( k2_xboole_0(k5_enumset1(X0_40,X0_40,X1_40,X2_40,X3_40,X4_40,X5_40),k5_enumset1(X6_40,X6_40,X6_40,X6_40,X6_40,X6_40,X6_40)) = k5_enumset1(X0_40,X1_40,X2_40,X3_40,X4_40,X5_40,X6_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_257,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_75,plain,
    ( X0_39 != X1_39
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != X1_39
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = X0_39 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_143,plain,
    ( X0_39 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = X0_39
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_256,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_150,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_74,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_43,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_37,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != X0_39
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != X0_39
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_42,plain,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_3,negated_conjecture,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1284,c_758,c_757,c_742,c_282,c_281,c_277,c_257,c_256,c_150,c_74,c_43,c_42,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:35:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.43/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/0.99  
% 2.43/0.99  ------  iProver source info
% 2.43/0.99  
% 2.43/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.43/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/0.99  git: non_committed_changes: false
% 2.43/0.99  git: last_make_outside_of_git: false
% 2.43/0.99  
% 2.43/0.99  ------ 
% 2.43/0.99  ------ Parsing...
% 2.43/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.43/0.99  ------ Proving...
% 2.43/0.99  ------ Problem Properties 
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  clauses                                 4
% 2.43/0.99  conjectures                             1
% 2.43/0.99  EPR                                     0
% 2.43/0.99  Horn                                    4
% 2.43/0.99  unary                                   4
% 2.43/0.99  binary                                  0
% 2.43/0.99  lits                                    4
% 2.43/0.99  lits eq                                 4
% 2.43/0.99  fd_pure                                 0
% 2.43/0.99  fd_pseudo                               0
% 2.43/0.99  fd_cond                                 0
% 2.43/0.99  fd_pseudo_cond                          0
% 2.43/0.99  AC symbols                              0
% 2.43/0.99  
% 2.43/0.99  ------ Input Options Time Limit: Unbounded
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  ------ 
% 2.43/0.99  Current options:
% 2.43/0.99  ------ 
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  ------ Proving...
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  % SZS status Theorem for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  fof(f1,axiom,(
% 2.43/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f17,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f1])).
% 2.43/0.99  
% 2.43/0.99  fof(f3,axiom,(
% 2.43/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f19,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f3])).
% 2.43/0.99  
% 2.43/0.99  fof(f5,axiom,(
% 2.43/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f21,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f5])).
% 2.43/0.99  
% 2.43/0.99  fof(f6,axiom,(
% 2.43/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f22,plain,(
% 2.43/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f6])).
% 2.43/0.99  
% 2.43/0.99  fof(f7,axiom,(
% 2.43/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f23,plain,(
% 2.43/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f7])).
% 2.43/0.99  
% 2.43/0.99  fof(f11,axiom,(
% 2.43/0.99    ! [X0,X1,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f27,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f11])).
% 2.43/0.99  
% 2.43/0.99  fof(f32,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f27,f25])).
% 2.43/0.99  
% 2.43/0.99  fof(f33,plain,(
% 2.43/0.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f23,f32])).
% 2.43/0.99  
% 2.43/0.99  fof(f34,plain,(
% 2.43/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f22,f33])).
% 2.43/0.99  
% 2.43/0.99  fof(f35,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f21,f34])).
% 2.43/0.99  
% 2.43/0.99  fof(f2,axiom,(
% 2.43/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f18,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f2])).
% 2.43/0.99  
% 2.43/0.99  fof(f10,axiom,(
% 2.43/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f26,plain,(
% 2.43/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f10])).
% 2.43/0.99  
% 2.43/0.99  fof(f29,plain,(
% 2.43/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f26,f25])).
% 2.43/0.99  
% 2.43/0.99  fof(f8,axiom,(
% 2.43/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f24,plain,(
% 2.43/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f8])).
% 2.43/0.99  
% 2.43/0.99  fof(f9,axiom,(
% 2.43/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f25,plain,(
% 2.43/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f9])).
% 2.43/0.99  
% 2.43/0.99  fof(f30,plain,(
% 2.43/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f24,f25])).
% 2.43/0.99  
% 2.43/0.99  fof(f31,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f18,f29,f30])).
% 2.43/0.99  
% 2.43/0.99  fof(f37,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))) )),
% 2.43/0.99    inference(definition_unfolding,[],[f19,f34,f35,f31])).
% 2.43/0.99  
% 2.43/0.99  fof(f4,axiom,(
% 2.43/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f20,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f4])).
% 2.43/0.99  
% 2.43/0.99  fof(f36,plain,(
% 2.43/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f20,f25,f34])).
% 2.43/0.99  
% 2.43/0.99  fof(f12,conjecture,(
% 2.43/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f13,negated_conjecture,(
% 2.43/0.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 2.43/0.99    inference(negated_conjecture,[],[f12])).
% 2.43/0.99  
% 2.43/0.99  fof(f14,plain,(
% 2.43/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 2.43/0.99    inference(ennf_transformation,[],[f13])).
% 2.43/0.99  
% 2.43/0.99  fof(f15,plain,(
% 2.43/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) => k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f16,plain,(
% 2.43/0.99    k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 2.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f15])).
% 2.43/0.99  
% 2.43/0.99  fof(f28,plain,(
% 2.43/0.99    k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 2.43/0.99    inference(cnf_transformation,[],[f16])).
% 2.43/0.99  
% 2.43/0.99  fof(f38,plain,(
% 2.43/0.99    k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8))),
% 2.43/0.99    inference(definition_unfolding,[],[f28,f33,f31])).
% 2.43/0.99  
% 2.43/0.99  cnf(c_16,plain,
% 2.43/0.99      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 2.43/0.99      theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_69,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != X0_39
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != X0_39 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1284,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_69]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1,plain,
% 2.43/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_13,plain,
% 2.43/0.99      ( k2_xboole_0(k2_xboole_0(X0_39,X1_39),X2_39) = k2_xboole_0(X0_39,k2_xboole_0(X1_39,X2_39)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_758,plain,
% 2.43/0.99      ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_84,plain,
% 2.43/0.99      ( k2_xboole_0(X0_39,X1_39) != X2_39
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != X2_39
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_39,X1_39) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_365,plain,
% 2.43/0.99      ( k2_xboole_0(X0_39,X1_39) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_39,X1_39)
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_84]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_757,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_365]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_17,plain,
% 2.43/0.99      ( X0_39 != X1_39
% 2.43/0.99      | X2_39 != X3_39
% 2.43/0.99      | k2_xboole_0(X0_39,X2_39) = k2_xboole_0(X1_39,X3_39) ),
% 2.43/0.99      theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_46,plain,
% 2.43/0.99      ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) != X0_39
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != X1_39
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X1_39,X0_39) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_354,plain,
% 2.43/0.99      ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) != X0_39
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0_39) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_742,plain,
% 2.43/0.99      ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_354]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_12,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(X0_40,X0_40,X0_40,X0_40,X0_40,X0_40,X0_40),k2_xboole_0(k5_enumset1(X1_40,X1_40,X1_40,X1_40,X1_40,X1_40,X1_40),k5_enumset1(X2_40,X3_40,X4_40,X5_40,X6_40,X7_40,X8_40))) = k2_xboole_0(k5_enumset1(X0_40,X0_40,X0_40,X0_40,X1_40,X2_40,X3_40),k5_enumset1(X4_40,X4_40,X4_40,X5_40,X6_40,X7_40,X8_40)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_282,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_149,plain,
% 2.43/0.99      ( k2_xboole_0(X0_39,X1_39) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_39,X1_39)
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_84]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_281,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_149]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_15,plain,( X0_39 = X0_39 ),theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_277,plain,
% 2.43/0.99      ( k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_0,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 2.43/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_14,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(X0_40,X0_40,X1_40,X2_40,X3_40,X4_40,X5_40),k5_enumset1(X6_40,X6_40,X6_40,X6_40,X6_40,X6_40,X6_40)) = k5_enumset1(X0_40,X1_40,X2_40,X3_40,X4_40,X5_40,X6_40) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_257,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_75,plain,
% 2.43/0.99      ( X0_39 != X1_39
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != X1_39
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = X0_39 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_143,plain,
% 2.43/0.99      ( X0_39 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = X0_39
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_75]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_256,plain,
% 2.43/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 2.43/0.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_143]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_150,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_74,plain,
% 2.43/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_43,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_37,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != X0_39
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != X0_39
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_42,plain,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8))
% 2.43/0.99      | k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_37]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3,negated_conjecture,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_11,negated_conjecture,
% 2.43/0.99      ( k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK5,sK6,sK7,sK8)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(contradiction,plain,
% 2.43/0.99      ( $false ),
% 2.43/0.99      inference(minisat,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1284,c_758,c_757,c_742,c_282,c_281,c_277,c_257,c_256,
% 2.43/0.99                 c_150,c_74,c_43,c_42,c_11]) ).
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  ------                               Statistics
% 2.43/0.99  
% 2.43/0.99  ------ Selected
% 2.43/0.99  
% 2.43/0.99  total_time:                             0.08
% 2.43/0.99  
%------------------------------------------------------------------------------
