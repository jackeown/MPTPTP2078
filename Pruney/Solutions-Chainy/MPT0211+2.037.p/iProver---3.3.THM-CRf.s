%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:29 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
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

cnf(c_111,plain,
    ( k1_enumset1(sK0,sK1,sK2) != X0_35
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_35
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_1416,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_111])).

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

cnf(c_838,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_131,plain,
    ( X0_35 != X1_35
    | k1_enumset1(sK0,sK1,sK2) != X1_35
    | k1_enumset1(sK0,sK1,sK2) = X0_35 ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_283,plain,
    ( X0_35 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_837,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_37,plain,
    ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_42,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
    inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1])).

cnf(c_246,plain,
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

cnf(c_187,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_169,plain,
    ( X0_35 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_186,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_40,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1])).

cnf(c_163,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_132,plain,
    ( X0_35 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_35
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_162,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_51,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_133,plain,
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
    inference(minisat,[status(thm)],[c_1416,c_838,c_837,c_246,c_187,c_186,c_163,c_162,c_133,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.54/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.04  
% 1.54/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.54/1.04  
% 1.54/1.04  ------  iProver source info
% 1.54/1.04  
% 1.54/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.54/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.54/1.04  git: non_committed_changes: false
% 1.54/1.04  git: last_make_outside_of_git: false
% 1.54/1.04  
% 1.54/1.04  ------ 
% 1.54/1.04  ------ Parsing...
% 1.54/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.54/1.04  
% 1.54/1.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.54/1.04  
% 1.54/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.54/1.04  
% 1.54/1.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.54/1.04  ------ Proving...
% 1.54/1.04  ------ Problem Properties 
% 1.54/1.04  
% 1.54/1.04  
% 1.54/1.04  clauses                                 12
% 1.54/1.04  conjectures                             1
% 1.54/1.04  EPR                                     0
% 1.54/1.04  Horn                                    12
% 1.54/1.04  unary                                   12
% 1.54/1.04  binary                                  0
% 1.54/1.04  lits                                    12
% 1.54/1.04  lits eq                                 12
% 1.54/1.04  fd_pure                                 0
% 1.54/1.04  fd_pseudo                               0
% 1.54/1.04  fd_cond                                 0
% 1.54/1.04  fd_pseudo_cond                          0
% 1.54/1.04  AC symbols                              1
% 1.54/1.04  
% 1.54/1.04  ------ Input Options Time Limit: Unbounded
% 1.54/1.04  
% 1.54/1.04  
% 1.54/1.04  ------ 
% 1.54/1.04  Current options:
% 1.54/1.04  ------ 
% 1.54/1.04  
% 1.54/1.04  
% 1.54/1.04  
% 1.54/1.04  
% 1.54/1.04  ------ Proving...
% 1.54/1.04  
% 1.54/1.04  
% 1.54/1.04  % SZS status Theorem for theBenchmark.p
% 1.54/1.04  
% 1.54/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.54/1.04  
% 1.54/1.04  fof(f8,axiom,(
% 1.54/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f33,plain,(
% 1.54/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f8])).
% 1.54/1.04  
% 1.54/1.04  fof(f6,axiom,(
% 1.54/1.04    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f31,plain,(
% 1.54/1.04    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f6])).
% 1.54/1.04  
% 1.54/1.04  fof(f4,axiom,(
% 1.54/1.04    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f29,plain,(
% 1.54/1.04    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f4])).
% 1.54/1.04  
% 1.54/1.04  fof(f17,axiom,(
% 1.54/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f42,plain,(
% 1.54/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f17])).
% 1.54/1.04  
% 1.54/1.04  fof(f47,plain,(
% 1.54/1.04    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/1.04    inference(definition_unfolding,[],[f31,f29,f42,f42])).
% 1.54/1.04  
% 1.54/1.04  fof(f54,plain,(
% 1.54/1.04    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)))) )),
% 1.54/1.04    inference(definition_unfolding,[],[f33,f47,f47])).
% 1.54/1.04  
% 1.54/1.04  fof(f3,axiom,(
% 1.54/1.04    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f28,plain,(
% 1.54/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f3])).
% 1.54/1.04  
% 1.54/1.04  fof(f1,axiom,(
% 1.54/1.04    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f26,plain,(
% 1.54/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f1])).
% 1.54/1.04  
% 1.54/1.04  fof(f5,axiom,(
% 1.54/1.04    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f30,plain,(
% 1.54/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f5])).
% 1.54/1.04  
% 1.54/1.04  fof(f2,axiom,(
% 1.54/1.04    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f27,plain,(
% 1.54/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f2])).
% 1.54/1.04  
% 1.54/1.04  fof(f53,plain,(
% 1.54/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/1.04    inference(definition_unfolding,[],[f30,f27,f29])).
% 1.54/1.04  
% 1.54/1.04  fof(f9,axiom,(
% 1.54/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f34,plain,(
% 1.54/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f9])).
% 1.54/1.04  
% 1.54/1.04  fof(f55,plain,(
% 1.54/1.04    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)))) )),
% 1.54/1.04    inference(definition_unfolding,[],[f34,f47,f47])).
% 1.54/1.04  
% 1.54/1.04  fof(f18,axiom,(
% 1.54/1.04    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f43,plain,(
% 1.54/1.04    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/1.04    inference(cnf_transformation,[],[f18])).
% 1.54/1.04  
% 1.54/1.04  fof(f52,plain,(
% 1.54/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 1.54/1.04    inference(definition_unfolding,[],[f43,f47])).
% 1.54/1.04  
% 1.54/1.04  fof(f21,conjecture,(
% 1.54/1.04    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 1.54/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.54/1.04  
% 1.54/1.04  fof(f22,negated_conjecture,(
% 1.54/1.04    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 1.54/1.04    inference(negated_conjecture,[],[f21])).
% 1.54/1.04  
% 1.54/1.04  fof(f23,plain,(
% 1.54/1.04    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 1.54/1.04    inference(ennf_transformation,[],[f22])).
% 1.54/1.04  
% 1.54/1.04  fof(f24,plain,(
% 1.54/1.04    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 1.54/1.04    introduced(choice_axiom,[])).
% 1.54/1.04  
% 1.54/1.04  fof(f25,plain,(
% 1.54/1.04    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 1.54/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 1.54/1.04  
% 1.54/1.04  fof(f46,plain,(
% 1.54/1.04    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 1.54/1.04    inference(cnf_transformation,[],[f25])).
% 1.54/1.04  
% 1.54/1.04  fof(f62,plain,(
% 1.54/1.04    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 1.54/1.04    inference(definition_unfolding,[],[f46,f29,f42,f42])).
% 1.54/1.04  
% 1.54/1.04  cnf(c_52,plain,
% 1.54/1.04      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 1.54/1.04      theory(equality) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_111,plain,
% 1.54/1.04      ( k1_enumset1(sK0,sK1,sK2) != X0_35
% 1.54/1.04      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_35
% 1.54/1.04      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_52]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_1416,plain,
% 1.54/1.04      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 1.54/1.04      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 1.54/1.04      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_111]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_4,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
% 1.54/1.04      inference(cnf_transformation,[],[f54]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_36,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 1.54/1.04      inference(subtyping,[status(esa)],[c_4]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_2,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 1.54/1.04      inference(cnf_transformation,[],[f28]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_1,plain,
% 1.54/1.04      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 1.54/1.04      inference(cnf_transformation,[],[f26]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_43,plain,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k5_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X3_36)))) ),
% 1.54/1.04      inference(theory_normalisation,[status(thm)],[c_36,c_2,c_1]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_838,plain,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_43]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_131,plain,
% 1.54/1.04      ( X0_35 != X1_35
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) != X1_35
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) = X0_35 ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_52]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_283,plain,
% 1.54/1.04      ( X0_35 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_131]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_837,plain,
% 1.54/1.04      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 1.54/1.04      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_283]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_3,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 1.54/1.04      inference(cnf_transformation,[],[f53]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_37,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(X0_35,X1_35),k3_xboole_0(X0_35,X1_35)) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 1.54/1.04      inference(subtyping,[status(esa)],[c_3]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_42,plain,
% 1.54/1.04      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X0_35,X1_35))) = k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) ),
% 1.54/1.04      inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_246,plain,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_42]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_5,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
% 1.54/1.04      inference(cnf_transformation,[],[f55]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_35,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36)),k3_xboole_0(k1_enumset1(X3_36,X3_36,X0_36),k1_enumset1(X2_36,X2_36,X1_36))) ),
% 1.54/1.04      inference(subtyping,[status(esa)],[c_5]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_44,plain,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k1_enumset1(X2_36,X2_36,X3_36)))) = k5_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X3_36),k1_enumset1(X2_36,X2_36,X0_36)))) ),
% 1.54/1.04      inference(theory_normalisation,[status(thm)],[c_35,c_2,c_1]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_187,plain,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_44]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_169,plain,
% 1.54/1.04      ( X0_35 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_131]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_186,plain,
% 1.54/1.04      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 1.54/1.04      | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_169]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_0,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 1.54/1.04      inference(cnf_transformation,[],[f52]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_40,plain,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 1.54/1.04      inference(subtyping,[status(esa)],[c_0]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_41,plain,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X1_36,X2_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 1.54/1.04      inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_163,plain,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_41]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_132,plain,
% 1.54/1.04      ( X0_35 != k1_enumset1(sK0,sK1,sK2)
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) = X0_35
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_131]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_162,plain,
% 1.54/1.04      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 1.54/1.04      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 1.54/1.04      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_132]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_51,plain,( X0_35 = X0_35 ),theory(equality) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_133,plain,
% 1.54/1.04      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(instantiation,[status(thm)],[c_51]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_12,negated_conjecture,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(cnf_transformation,[],[f62]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_29,negated_conjecture,
% 1.54/1.04      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(subtyping,[status(esa)],[c_12]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(c_50,negated_conjecture,
% 1.54/1.04      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 1.54/1.04      inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1]) ).
% 1.54/1.04  
% 1.54/1.04  cnf(contradiction,plain,
% 1.54/1.04      ( $false ),
% 1.54/1.04      inference(minisat,
% 1.54/1.04                [status(thm)],
% 1.54/1.04                [c_1416,c_838,c_837,c_246,c_187,c_186,c_163,c_162,c_133,
% 1.54/1.04                 c_50]) ).
% 1.54/1.04  
% 1.54/1.04  
% 1.54/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.54/1.04  
% 1.54/1.04  ------                               Statistics
% 1.54/1.04  
% 1.54/1.04  ------ Selected
% 1.54/1.04  
% 1.54/1.04  total_time:                             0.119
% 1.54/1.04  
%------------------------------------------------------------------------------
