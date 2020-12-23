%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:29 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
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
fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f29,f42,f42])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(definition_unfolding,[],[f33,f47,f47])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f30,f27,f29])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f34,f47,f47])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f21,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f46,f29,f42,f42])).

cnf(c_52,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_113,plain,
    ( k1_enumset1(sK0,sK1,sK2) != X0_35
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_35
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_2295,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_43,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_36,c_2,c_1])).

cnf(c_860,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_133,plain,
    ( X0_35 != X1_35
    | k1_enumset1(sK0,sK1,sK2) != X1_35
    | k1_enumset1(sK0,sK1,sK2) = X0_35 ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_285,plain,
    ( X0_35 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_859,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_37,plain,
    ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_42,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1])).

cnf(c_247,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_44,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
    inference(theory_normalisation,[status(thm)],[c_35,c_2,c_1])).

cnf(c_189,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_171,plain,
    ( X0_35 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_188,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_40,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1])).

cnf(c_165,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_134,plain,
    ( X0_35 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_164,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_51,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_135,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_50,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2295,c_860,c_859,c_247,c_189,c_188,c_165,c_164,c_135,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.68/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/0.98  
% 2.68/0.98  ------  iProver source info
% 2.68/0.98  
% 2.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/0.98  git: non_committed_changes: false
% 2.68/0.98  git: last_make_outside_of_git: false
% 2.68/0.98  
% 2.68/0.98  ------ 
% 2.68/0.98  ------ Parsing...
% 2.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.68/0.98  ------ Proving...
% 2.68/0.98  ------ Problem Properties 
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  clauses                                 12
% 2.68/0.98  conjectures                             1
% 2.68/0.98  EPR                                     0
% 2.68/0.98  Horn                                    12
% 2.68/0.98  unary                                   12
% 2.68/0.98  binary                                  0
% 2.68/0.98  lits                                    12
% 2.68/0.98  lits eq                                 12
% 2.68/0.98  fd_pure                                 0
% 2.68/0.98  fd_pseudo                               0
% 2.68/0.98  fd_cond                                 0
% 2.68/0.98  fd_pseudo_cond                          0
% 2.68/0.98  AC symbols                              1
% 2.68/0.98  
% 2.68/0.98  ------ Input Options Time Limit: Unbounded
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  ------ 
% 2.68/0.98  Current options:
% 2.68/0.98  ------ 
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  ------ Proving...
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  % SZS status Theorem for theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  fof(f8,axiom,(
% 2.68/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f33,plain,(
% 2.68/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f8])).
% 2.68/0.98  
% 2.68/0.98  fof(f6,axiom,(
% 2.68/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f31,plain,(
% 2.68/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f6])).
% 2.68/0.98  
% 2.68/0.98  fof(f4,axiom,(
% 2.68/0.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f29,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f4])).
% 2.68/0.98  
% 2.68/0.98  fof(f17,axiom,(
% 2.68/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f42,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f17])).
% 2.68/0.98  
% 2.68/0.98  fof(f47,plain,(
% 2.68/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.68/0.98    inference(definition_unfolding,[],[f31,f29,f42,f42])).
% 2.68/0.98  
% 2.68/0.98  fof(f54,plain,(
% 2.68/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)))) )),
% 2.68/0.98    inference(definition_unfolding,[],[f33,f47,f47])).
% 2.68/0.98  
% 2.68/0.98  fof(f3,axiom,(
% 2.68/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f28,plain,(
% 2.68/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f3])).
% 2.68/0.98  
% 2.68/0.98  fof(f1,axiom,(
% 2.68/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f26,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f1])).
% 2.68/0.98  
% 2.68/0.98  fof(f5,axiom,(
% 2.68/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f30,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f5])).
% 2.68/0.98  
% 2.68/0.98  fof(f2,axiom,(
% 2.68/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f27,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f2])).
% 2.68/0.98  
% 2.68/0.98  fof(f53,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.68/0.98    inference(definition_unfolding,[],[f30,f27,f29])).
% 2.68/0.98  
% 2.68/0.98  fof(f9,axiom,(
% 2.68/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f34,plain,(
% 2.68/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f9])).
% 2.68/0.98  
% 2.68/0.98  fof(f55,plain,(
% 2.68/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)))) )),
% 2.68/0.98    inference(definition_unfolding,[],[f34,f47,f47])).
% 2.68/0.98  
% 2.68/0.98  fof(f18,axiom,(
% 2.68/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f43,plain,(
% 2.68/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f18])).
% 2.68/0.98  
% 2.68/0.98  fof(f52,plain,(
% 2.68/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.68/0.98    inference(definition_unfolding,[],[f43,f47])).
% 2.68/0.98  
% 2.68/0.98  fof(f21,conjecture,(
% 2.68/0.98    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f22,negated_conjecture,(
% 2.68/0.98    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.68/0.98    inference(negated_conjecture,[],[f21])).
% 2.68/0.98  
% 2.68/0.98  fof(f23,plain,(
% 2.68/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.68/0.98    inference(ennf_transformation,[],[f22])).
% 2.68/0.98  
% 2.68/0.98  fof(f24,plain,(
% 2.68/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.68/0.98    introduced(choice_axiom,[])).
% 2.68/0.98  
% 2.68/0.98  fof(f25,plain,(
% 2.68/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 2.68/0.98  
% 2.68/0.98  fof(f46,plain,(
% 2.68/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.68/0.98    inference(cnf_transformation,[],[f25])).
% 2.68/0.98  
% 2.68/0.98  fof(f62,plain,(
% 2.68/0.98    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.68/0.98    inference(definition_unfolding,[],[f46,f29,f42,f42])).
% 2.68/0.98  
% 2.68/0.98  cnf(c_52,plain,
% 2.68/0.98      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 2.68/0.98      theory(equality) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_113,plain,
% 2.68/0.98      ( k1_enumset1(sK0,sK1,sK2) != X0_35
% 2.68/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_35
% 2.68/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.98      inference(instantiation,[status(thm)],[c_52]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2295,plain,
% 2.68/0.98      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.68/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 2.68/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_113]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_4,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_36,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.68/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1,plain,
% 2.68/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_43,plain,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
% 2.68/0.99      inference(theory_normalisation,[status(thm)],[c_36,c_2,c_1]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_860,plain,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_133,plain,
% 2.68/0.99      ( X0_35 != X1_35
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) != X1_35
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_35 ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_52]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_285,plain,
% 2.68/0.99      ( X0_35 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_133]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_859,plain,
% 2.68/0.99      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.68/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_285]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_37,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_42,plain,
% 2.68/0.99      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 2.68/0.99      inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_247,plain,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_42]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_5,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_35,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_44,plain,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
% 2.68/0.99      inference(theory_normalisation,[status(thm)],[c_35,c_2,c_1]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_189,plain,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_44]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_171,plain,
% 2.68/0.99      ( X0_35 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_133]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_188,plain,
% 2.68/0.99      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.68/0.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_171]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_0,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.68/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_40,plain,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_41,plain,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 2.68/0.99      inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_165,plain,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_41]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_134,plain,
% 2.68/0.99      ( X0_35 != k1_enumset1(sK0,sK1,sK2)
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_133]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_164,plain,
% 2.68/0.99      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 2.68/0.99      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.68/0.99      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_134]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_51,plain,( X0_35 = X0_35 ),theory(equality) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_135,plain,
% 2.68/0.99      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_51]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_12,negated_conjecture,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_29,negated_conjecture,
% 2.68/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_50,negated_conjecture,
% 2.68/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(contradiction,plain,
% 2.68/0.99      ( $false ),
% 2.68/0.99      inference(minisat,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_2295,c_860,c_859,c_247,c_189,c_188,c_165,c_164,c_135,
% 2.68/0.99                 c_50]) ).
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  ------                               Statistics
% 2.68/0.99  
% 2.68/0.99  ------ Selected
% 2.68/0.99  
% 2.68/0.99  total_time:                             0.148
% 2.68/0.99  
%------------------------------------------------------------------------------
