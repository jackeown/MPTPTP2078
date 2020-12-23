%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:28 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 141 expanded)
%              Number of clauses        :   34 (  47 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 172 expanded)
%              Number of equality atoms :   86 ( 171 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f29,f41,f41])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(definition_unfolding,[],[f34,f47,f47])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f30,f27,f29])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f35,f47,f47])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f21,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f46,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f46,f29,f41,f41])).

cnf(c_52,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_101,plain,
    ( k1_enumset1(sK0,sK1,sK2) != X0_35
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_35
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_1935,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_35,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_44,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_35,c_2,c_1])).

cnf(c_874,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_121,plain,
    ( X0_35 != X1_35
    | k1_enumset1(sK0,sK1,sK2) != X1_35
    | k1_enumset1(sK0,sK1,sK2) = X0_35 ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_479,plain,
    ( X0_35 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_873,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_37,plain,
    ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_42,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1])).

cnf(c_236,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_34,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_45,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1])).

cnf(c_179,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_159,plain,
    ( X0_35 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_178,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_40,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1])).

cnf(c_153,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_122,plain,
    ( X0_35 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_152,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_51,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_123,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_50,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1935,c_874,c_873,c_236,c_179,c_178,c_153,c_152,c_123,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:02:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.75/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.75/1.00  
% 2.75/1.00  ------  iProver source info
% 2.75/1.00  
% 2.75/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.75/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.75/1.00  git: non_committed_changes: false
% 2.75/1.00  git: last_make_outside_of_git: false
% 2.75/1.00  
% 2.75/1.00  ------ 
% 2.75/1.00  ------ Parsing...
% 2.75/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.75/1.00  ------ Proving...
% 2.75/1.00  ------ Problem Properties 
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  clauses                                 12
% 2.75/1.00  conjectures                             1
% 2.75/1.00  EPR                                     0
% 2.75/1.00  Horn                                    12
% 2.75/1.00  unary                                   12
% 2.75/1.00  binary                                  0
% 2.75/1.00  lits                                    12
% 2.75/1.00  lits eq                                 12
% 2.75/1.00  fd_pure                                 0
% 2.75/1.00  fd_pseudo                               0
% 2.75/1.00  fd_cond                                 0
% 2.75/1.00  fd_pseudo_cond                          0
% 2.75/1.00  AC symbols                              1
% 2.75/1.00  
% 2.75/1.00  ------ Input Options Time Limit: Unbounded
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  ------ 
% 2.75/1.00  Current options:
% 2.75/1.00  ------ 
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  ------ Proving...
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  % SZS status Theorem for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  fof(f9,axiom,(
% 2.75/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f34,plain,(
% 2.75/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f9])).
% 2.75/1.00  
% 2.75/1.00  fof(f6,axiom,(
% 2.75/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f31,plain,(
% 2.75/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f6])).
% 2.75/1.00  
% 2.75/1.00  fof(f4,axiom,(
% 2.75/1.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f29,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f4])).
% 2.75/1.00  
% 2.75/1.00  fof(f16,axiom,(
% 2.75/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f41,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f16])).
% 2.75/1.00  
% 2.75/1.00  fof(f47,plain,(
% 2.75/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.75/1.00    inference(definition_unfolding,[],[f31,f29,f41,f41])).
% 2.75/1.00  
% 2.75/1.00  fof(f54,plain,(
% 2.75/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)))) )),
% 2.75/1.00    inference(definition_unfolding,[],[f34,f47,f47])).
% 2.75/1.00  
% 2.75/1.00  fof(f3,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f28,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f3])).
% 2.75/1.00  
% 2.75/1.00  fof(f1,axiom,(
% 2.75/1.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f26,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f1])).
% 2.75/1.00  
% 2.75/1.00  fof(f5,axiom,(
% 2.75/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f30,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f5])).
% 2.75/1.00  
% 2.75/1.00  fof(f2,axiom,(
% 2.75/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f27,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f2])).
% 2.75/1.00  
% 2.75/1.00  fof(f52,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.75/1.00    inference(definition_unfolding,[],[f30,f27,f29])).
% 2.75/1.00  
% 2.75/1.00  fof(f10,axiom,(
% 2.75/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f35,plain,(
% 2.75/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f10])).
% 2.75/1.00  
% 2.75/1.00  fof(f55,plain,(
% 2.75/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)))) )),
% 2.75/1.00    inference(definition_unfolding,[],[f35,f47,f47])).
% 2.75/1.00  
% 2.75/1.00  fof(f17,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f42,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f17])).
% 2.75/1.00  
% 2.75/1.00  fof(f51,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.75/1.00    inference(definition_unfolding,[],[f42,f47])).
% 2.75/1.00  
% 2.75/1.00  fof(f21,conjecture,(
% 2.75/1.00    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f22,negated_conjecture,(
% 2.75/1.00    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.75/1.00    inference(negated_conjecture,[],[f21])).
% 2.75/1.00  
% 2.75/1.00  fof(f23,plain,(
% 2.75/1.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.75/1.00    inference(ennf_transformation,[],[f22])).
% 2.75/1.00  
% 2.75/1.00  fof(f24,plain,(
% 2.75/1.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.75/1.00    introduced(choice_axiom,[])).
% 2.75/1.00  
% 2.75/1.00  fof(f25,plain,(
% 2.75/1.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 2.75/1.00  
% 2.75/1.00  fof(f46,plain,(
% 2.75/1.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.75/1.00    inference(cnf_transformation,[],[f25])).
% 2.75/1.00  
% 2.75/1.00  fof(f61,plain,(
% 2.75/1.00    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.75/1.00    inference(definition_unfolding,[],[f46,f29,f41,f41])).
% 2.75/1.00  
% 2.75/1.00  cnf(c_52,plain,
% 2.75/1.00      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 2.75/1.00      theory(equality) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_101,plain,
% 2.75/1.00      ( k1_enumset1(sK0,sK1,sK2) != X0_35
% 2.75/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_35
% 2.75/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_52]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1935,plain,
% 2.75/1.00      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.75/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 2.75/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_101]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_5,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
% 2.75/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_35,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 2.75/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.75/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1,plain,
% 2.75/1.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_44,plain,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
% 2.75/1.00      inference(theory_normalisation,[status(thm)],[c_35,c_2,c_1]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_874,plain,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_44]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_121,plain,
% 2.75/1.00      ( X0_35 != X1_35
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) != X1_35
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) = X0_35 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_52]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_479,plain,
% 2.75/1.00      ( X0_35 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_121]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_873,plain,
% 2.75/1.00      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.75/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_479]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.75/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_37,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 2.75/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_42,plain,
% 2.75/1.00      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 2.75/1.00      inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_236,plain,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_42]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
% 2.75/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_34,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 2.75/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_45,plain,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
% 2.75/1.00      inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_179,plain,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_45]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_159,plain,
% 2.75/1.00      ( X0_35 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_121]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_178,plain,
% 2.75/1.00      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.75/1.00      | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_159]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_0,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.75/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_40,plain,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.75/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_41,plain,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.75/1.00      inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_153,plain,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_41]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_122,plain,
% 2.75/1.00      ( X0_35 != k1_enumset1(sK0,sK1,sK2)
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_121]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_152,plain,
% 2.75/1.00      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 2.75/1.00      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.75/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_122]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_51,plain,( X0_35 = X0_35 ),theory(equality) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_123,plain,
% 2.75/1.00      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_51]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_12,negated_conjecture,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_29,negated_conjecture,
% 2.75/1.00      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_50,negated_conjecture,
% 2.75/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.75/1.00      inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(contradiction,plain,
% 2.75/1.00      ( $false ),
% 2.75/1.00      inference(minisat,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_1935,c_874,c_873,c_236,c_179,c_178,c_153,c_152,c_123,
% 2.75/1.00                 c_50]) ).
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  ------                               Statistics
% 2.75/1.00  
% 2.75/1.00  ------ Selected
% 2.75/1.00  
% 2.75/1.00  total_time:                             0.149
% 2.75/1.00  
%------------------------------------------------------------------------------
