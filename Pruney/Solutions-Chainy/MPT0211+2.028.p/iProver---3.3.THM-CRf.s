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
% DateTime   : Thu Dec  3 11:28:27 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 120 expanded)
%              Number of clauses        :   28 (  37 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 143 expanded)
%              Number of equality atoms :   71 ( 142 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f28,f41,f41])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))) ),
    inference(definition_unfolding,[],[f30,f45,f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f34,f45,f45])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f45])).

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

fof(f59,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f44,f28,f41,f41])).

cnf(c_48,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_94,plain,
    ( k1_enumset1(sK0,sK1,sK2) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_468,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_33,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_40,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1])).

cnf(c_231,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_42,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1])).

cnf(c_172,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_114,plain,
    ( X0_34 != X1_34
    | k1_enumset1(sK0,sK1,sK2) != X1_34
    | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_152,plain,
    ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_171,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_37,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_38,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1])).

cnf(c_146,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_115,plain,
    ( X0_34 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_145,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_47,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_116,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_46,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_468,c_231,c_172,c_171,c_146,c_145,c_116,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.45/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.45/1.05  
% 0.45/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.45/1.05  
% 0.45/1.05  ------  iProver source info
% 0.45/1.05  
% 0.45/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.45/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.45/1.05  git: non_committed_changes: false
% 0.45/1.05  git: last_make_outside_of_git: false
% 0.45/1.05  
% 0.45/1.05  ------ 
% 0.45/1.05  ------ Parsing...
% 0.45/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.45/1.05  
% 0.45/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.45/1.05  
% 0.45/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.45/1.05  
% 0.45/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.45/1.05  ------ Proving...
% 0.45/1.05  ------ Problem Properties 
% 0.45/1.05  
% 0.45/1.05  
% 0.45/1.05  clauses                                 11
% 0.45/1.05  conjectures                             1
% 0.45/1.05  EPR                                     0
% 0.45/1.05  Horn                                    11
% 0.45/1.05  unary                                   11
% 0.45/1.05  binary                                  0
% 0.45/1.05  lits                                    11
% 0.45/1.05  lits eq                                 11
% 0.45/1.05  fd_pure                                 0
% 0.45/1.05  fd_pseudo                               0
% 0.45/1.05  fd_cond                                 0
% 0.45/1.05  fd_pseudo_cond                          0
% 0.45/1.05  AC symbols                              1
% 0.45/1.05  
% 0.45/1.05  ------ Input Options Time Limit: Unbounded
% 0.45/1.05  
% 0.45/1.05  
% 0.45/1.05  ------ 
% 0.45/1.05  Current options:
% 0.45/1.05  ------ 
% 0.45/1.05  
% 0.45/1.05  
% 0.45/1.05  
% 0.45/1.05  
% 0.45/1.05  ------ Proving...
% 0.45/1.05  
% 0.45/1.05  
% 0.45/1.05  % SZS status Theorem for theBenchmark.p
% 0.45/1.05  
% 0.45/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.45/1.05  
% 0.45/1.05  fof(f6,axiom,(
% 0.45/1.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f30,plain,(
% 0.45/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f6])).
% 0.45/1.05  
% 0.45/1.05  fof(f7,axiom,(
% 0.45/1.05    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f31,plain,(
% 0.45/1.05    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f7])).
% 0.45/1.05  
% 0.45/1.05  fof(f4,axiom,(
% 0.45/1.05    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f28,plain,(
% 0.45/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f4])).
% 0.45/1.05  
% 0.45/1.05  fof(f17,axiom,(
% 0.45/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f41,plain,(
% 0.45/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f17])).
% 0.45/1.05  
% 0.45/1.05  fof(f45,plain,(
% 0.45/1.05    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.45/1.05    inference(definition_unfolding,[],[f31,f28,f41,f41])).
% 0.45/1.05  
% 0.45/1.05  fof(f52,plain,(
% 0.45/1.05    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) )),
% 0.45/1.05    inference(definition_unfolding,[],[f30,f45,f45])).
% 0.45/1.05  
% 0.45/1.05  fof(f3,axiom,(
% 0.45/1.05    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f27,plain,(
% 0.45/1.05    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f3])).
% 0.45/1.05  
% 0.45/1.05  fof(f1,axiom,(
% 0.45/1.05    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f25,plain,(
% 0.45/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f1])).
% 0.45/1.05  
% 0.45/1.05  fof(f10,axiom,(
% 0.45/1.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f34,plain,(
% 0.45/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f10])).
% 0.45/1.05  
% 0.45/1.05  fof(f54,plain,(
% 0.45/1.05    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)))) )),
% 0.45/1.05    inference(definition_unfolding,[],[f34,f45,f45])).
% 0.45/1.05  
% 0.45/1.05  fof(f18,axiom,(
% 0.45/1.05    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f42,plain,(
% 0.45/1.05    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.45/1.05    inference(cnf_transformation,[],[f18])).
% 0.45/1.05  
% 0.45/1.05  fof(f50,plain,(
% 0.45/1.05    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 0.45/1.05    inference(definition_unfolding,[],[f42,f45])).
% 0.45/1.05  
% 0.45/1.05  fof(f20,conjecture,(
% 0.45/1.05    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 0.45/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.45/1.05  
% 0.45/1.05  fof(f21,negated_conjecture,(
% 0.45/1.05    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 0.45/1.05    inference(negated_conjecture,[],[f20])).
% 0.45/1.05  
% 0.45/1.05  fof(f22,plain,(
% 0.45/1.05    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 0.45/1.05    inference(ennf_transformation,[],[f21])).
% 0.45/1.05  
% 0.45/1.05  fof(f23,plain,(
% 0.45/1.05    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 0.45/1.05    introduced(choice_axiom,[])).
% 0.45/1.05  
% 0.45/1.05  fof(f24,plain,(
% 0.45/1.05    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 0.45/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 0.45/1.05  
% 0.45/1.05  fof(f44,plain,(
% 0.45/1.05    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 0.45/1.05    inference(cnf_transformation,[],[f24])).
% 0.45/1.05  
% 0.45/1.05  fof(f59,plain,(
% 0.45/1.05    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 0.45/1.05    inference(definition_unfolding,[],[f44,f28,f41,f41])).
% 0.45/1.05  
% 0.45/1.05  cnf(c_48,plain,
% 0.45/1.05      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 0.45/1.05      theory(equality) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_94,plain,
% 0.45/1.05      ( k1_enumset1(sK0,sK1,sK2) != X0_34
% 0.45/1.05      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
% 0.45/1.05      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_48]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_468,plain,
% 0.45/1.05      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 0.45/1.05      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 0.45/1.05      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_94]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_4,plain,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))) ),
% 0.45/1.05      inference(cnf_transformation,[],[f52]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_33,plain,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35))) ),
% 0.45/1.05      inference(subtyping,[status(esa)],[c_4]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_2,plain,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 0.45/1.05      inference(cnf_transformation,[],[f27]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_1,plain,
% 0.45/1.05      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 0.45/1.05      inference(cnf_transformation,[],[f25]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_40,plain,
% 0.45/1.05      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
% 0.45/1.05      inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_231,plain,
% 0.45/1.05      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_40]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_6,plain,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
% 0.45/1.05      inference(cnf_transformation,[],[f54]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_31,plain,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
% 0.45/1.05      inference(subtyping,[status(esa)],[c_6]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_42,plain,
% 0.45/1.05      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
% 0.45/1.05      inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_172,plain,
% 0.45/1.05      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_42]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_114,plain,
% 0.45/1.05      ( X0_34 != X1_34
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) != X1_34
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_48]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_152,plain,
% 0.45/1.05      ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_114]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_171,plain,
% 0.45/1.05      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 0.45/1.05      | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_152]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_0,plain,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 0.45/1.05      inference(cnf_transformation,[],[f50]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_37,plain,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 0.45/1.05      inference(subtyping,[status(esa)],[c_0]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_38,plain,
% 0.45/1.05      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 0.45/1.05      inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_146,plain,
% 0.45/1.05      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_38]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_115,plain,
% 0.45/1.05      ( X0_34 != k1_enumset1(sK0,sK1,sK2)
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_114]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_145,plain,
% 0.45/1.05      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 0.45/1.05      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 0.45/1.05      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_115]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_47,plain,( X0_34 = X0_34 ),theory(equality) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_116,plain,
% 0.45/1.05      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(instantiation,[status(thm)],[c_47]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_11,negated_conjecture,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(cnf_transformation,[],[f59]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_27,negated_conjecture,
% 0.45/1.05      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(subtyping,[status(esa)],[c_11]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(c_46,negated_conjecture,
% 0.45/1.05      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 0.45/1.05      inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1]) ).
% 0.45/1.05  
% 0.45/1.05  cnf(contradiction,plain,
% 0.45/1.05      ( $false ),
% 0.45/1.05      inference(minisat,
% 0.45/1.05                [status(thm)],
% 0.45/1.05                [c_468,c_231,c_172,c_171,c_146,c_145,c_116,c_46]) ).
% 0.45/1.05  
% 0.45/1.05  
% 0.45/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.45/1.05  
% 0.45/1.05  ------                               Statistics
% 0.45/1.05  
% 0.45/1.05  ------ Selected
% 0.45/1.05  
% 0.45/1.05  total_time:                             0.067
% 0.45/1.05  
%------------------------------------------------------------------------------
