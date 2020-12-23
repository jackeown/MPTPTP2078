%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:04 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 202 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 215 expanded)
%              Number of equality atoms :   56 ( 214 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f26,f22,f38,f38])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
    inference(definition_unfolding,[],[f24,f39,f39])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) ),
    inference(definition_unfolding,[],[f23,f39,f39])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
    inference(definition_unfolding,[],[f25,f39,f39])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) ),
    inference(ennf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f36,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
    inference(definition_unfolding,[],[f36,f39,f39])).

cnf(c_3,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,plain,
    ( k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X3_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37))) = k5_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X0_37),k4_xboole_0(k6_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X1_37),k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X0_37))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_542,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_116,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) != X0_35
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != X0_35
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_541,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0)))
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_2,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,plain,
    ( k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X3_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37))) = k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X3_37),k4_xboole_0(k6_enumset1(X1_37,X1_37,X1_37,X1_37,X1_37,X1_37,X1_37,X2_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X3_37))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_240,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_4,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X0),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,plain,
    ( k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X3_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37))) = k5_xboole_0(k6_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X0_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X1_37),k6_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X0_37))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_97,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_74,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != X0_35
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != X0_35
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_96,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0)))
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0)))
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_542,c_541,c_240,c_97,c_96,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:13:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.07/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/1.00  
% 2.07/1.00  ------  iProver source info
% 2.07/1.00  
% 2.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/1.00  git: non_committed_changes: false
% 2.07/1.00  git: last_make_outside_of_git: false
% 2.07/1.00  
% 2.07/1.00  ------ 
% 2.07/1.00  ------ Parsing...
% 2.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.07/1.00  ------ Proving...
% 2.07/1.00  ------ Problem Properties 
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  clauses                                 9
% 2.07/1.00  conjectures                             1
% 2.07/1.00  EPR                                     0
% 2.07/1.00  Horn                                    9
% 2.07/1.00  unary                                   9
% 2.07/1.00  binary                                  0
% 2.07/1.00  lits                                    9
% 2.07/1.00  lits eq                                 9
% 2.07/1.00  fd_pure                                 0
% 2.07/1.00  fd_pseudo                               0
% 2.07/1.00  fd_cond                                 0
% 2.07/1.00  fd_pseudo_cond                          0
% 2.07/1.00  AC symbols                              0
% 2.07/1.00  
% 2.07/1.00  ------ Input Options Time Limit: Unbounded
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  ------ 
% 2.07/1.00  Current options:
% 2.07/1.00  ------ 
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  ------ Proving...
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  % SZS status Theorem for theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  fof(f4,axiom,(
% 2.07/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f24,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f4])).
% 2.07/1.00  
% 2.07/1.00  fof(f6,axiom,(
% 2.07/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f26,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f6])).
% 2.07/1.00  
% 2.07/1.00  fof(f2,axiom,(
% 2.07/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f22,plain,(
% 2.07/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.07/1.00    inference(cnf_transformation,[],[f2])).
% 2.07/1.00  
% 2.07/1.00  fof(f15,axiom,(
% 2.07/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f35,plain,(
% 2.07/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f15])).
% 2.07/1.00  
% 2.07/1.00  fof(f14,axiom,(
% 2.07/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f34,plain,(
% 2.07/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f14])).
% 2.07/1.00  
% 2.07/1.00  fof(f13,axiom,(
% 2.07/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f33,plain,(
% 2.07/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f13])).
% 2.07/1.00  
% 2.07/1.00  fof(f37,plain,(
% 2.07/1.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.07/1.00    inference(definition_unfolding,[],[f34,f33])).
% 2.07/1.00  
% 2.07/1.00  fof(f38,plain,(
% 2.07/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.07/1.00    inference(definition_unfolding,[],[f35,f37])).
% 2.07/1.00  
% 2.07/1.00  fof(f39,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.07/1.00    inference(definition_unfolding,[],[f26,f22,f38,f38])).
% 2.07/1.00  
% 2.07/1.00  fof(f45,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))) )),
% 2.07/1.00    inference(definition_unfolding,[],[f24,f39,f39])).
% 2.07/1.00  
% 2.07/1.00  fof(f3,axiom,(
% 2.07/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f23,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f3])).
% 2.07/1.00  
% 2.07/1.00  fof(f44,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) )),
% 2.07/1.00    inference(definition_unfolding,[],[f23,f39,f39])).
% 2.07/1.00  
% 2.07/1.00  fof(f5,axiom,(
% 2.07/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f25,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f5])).
% 2.07/1.00  
% 2.07/1.00  fof(f46,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))) )),
% 2.07/1.00    inference(definition_unfolding,[],[f25,f39,f39])).
% 2.07/1.00  
% 2.07/1.00  fof(f16,conjecture,(
% 2.07/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f17,negated_conjecture,(
% 2.07/1.00    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 2.07/1.00    inference(negated_conjecture,[],[f16])).
% 2.07/1.00  
% 2.07/1.00  fof(f18,plain,(
% 2.07/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)),
% 2.07/1.00    inference(ennf_transformation,[],[f17])).
% 2.07/1.00  
% 2.07/1.00  fof(f19,plain,(
% 2.07/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 2.07/1.00    introduced(choice_axiom,[])).
% 2.07/1.00  
% 2.07/1.00  fof(f20,plain,(
% 2.07/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 2.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 2.07/1.00  
% 2.07/1.00  fof(f36,plain,(
% 2.07/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 2.07/1.00    inference(cnf_transformation,[],[f20])).
% 2.07/1.00  
% 2.07/1.00  fof(f50,plain,(
% 2.07/1.00    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)))),
% 2.07/1.00    inference(definition_unfolding,[],[f36,f39,f39])).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_24,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X3_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37))) = k5_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X0_37),k4_xboole_0(k6_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X1_37),k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X0_37))) ),
% 2.07/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_542,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_30,plain,
% 2.07/1.00      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 2.07/1.00      theory(equality) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_116,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) != X0_35
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != X0_35
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_541,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0)))
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_116]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_25,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X3_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37))) = k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X3_37),k4_xboole_0(k6_enumset1(X1_37,X1_37,X1_37,X1_37,X1_37,X1_37,X1_37,X2_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X3_37))) ),
% 2.07/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_240,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X0),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X0))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_23,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X3_37),k6_enumset1(X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X0_37,X1_37))) = k5_xboole_0(k6_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X0_37),k4_xboole_0(k6_enumset1(X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X2_37,X1_37),k6_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X3_37,X0_37))) ),
% 2.07/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_97,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0))) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_74,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != X0_35
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != X0_35
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_96,plain,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0)))
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK0)))
% 2.07/1.00      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_74]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_8,negated_conjecture,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_19,negated_conjecture,
% 2.07/1.00      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))) ),
% 2.07/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(contradiction,plain,
% 2.07/1.00      ( $false ),
% 2.07/1.00      inference(minisat,[status(thm)],[c_542,c_541,c_240,c_97,c_96,c_19]) ).
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  ------                               Statistics
% 2.07/1.00  
% 2.07/1.00  ------ Selected
% 2.07/1.00  
% 2.07/1.00  total_time:                             0.082
% 2.07/1.00  
%------------------------------------------------------------------------------
