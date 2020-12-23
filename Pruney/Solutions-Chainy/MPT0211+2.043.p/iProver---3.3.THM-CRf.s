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
% DateTime   : Thu Dec  3 11:28:30 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 117 expanded)
%              Number of clauses        :   27 (  34 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 134 expanded)
%              Number of equality atoms :   68 ( 133 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f31,f46,f46])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(definition_unfolding,[],[f34,f51,f51])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X0)),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X0))) ),
    inference(definition_unfolding,[],[f36,f51,f51])).

fof(f23,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f23])).

fof(f25,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f24])).

fof(f26,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).

fof(f50,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f50,f31,f46,f46])).

cnf(c_54,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_167,plain,
    ( X0_34 != X1_34
    | X0_34 = k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) != X1_34 ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_177,plain,
    ( X0_34 = k1_enumset1(sK0,sK1,sK2)
    | X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_263,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_43,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_36,c_2,c_1])).

cnf(c_198,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_40,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1])).

cnf(c_165,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_133,plain,
    ( X0_34 != X1_34
    | k1_enumset1(sK0,sK1,sK2) != X1_34
    | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_158,plain,
    ( X0_34 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_164,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_53,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_159,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_45,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X3_35,X3_35,X2_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_52,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1])).

cnf(c_83,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_45,c_52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_263,c_198,c_165,c_164,c_159,c_83])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:35:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.30/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/0.99  
% 2.30/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.30/0.99  
% 2.30/0.99  ------  iProver source info
% 2.30/0.99  
% 2.30/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.30/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.30/0.99  git: non_committed_changes: false
% 2.30/0.99  git: last_make_outside_of_git: false
% 2.30/0.99  
% 2.30/0.99  ------ 
% 2.30/0.99  ------ Parsing...
% 2.30/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.30/0.99  
% 2.30/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.30/0.99  
% 2.30/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.30/0.99  
% 2.30/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.30/0.99  ------ Proving...
% 2.30/0.99  ------ Problem Properties 
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  clauses                                 14
% 2.30/0.99  conjectures                             1
% 2.30/0.99  EPR                                     0
% 2.30/0.99  Horn                                    14
% 2.30/0.99  unary                                   14
% 2.30/0.99  binary                                  0
% 2.30/0.99  lits                                    14
% 2.30/0.99  lits eq                                 14
% 2.30/0.99  fd_pure                                 0
% 2.30/0.99  fd_pseudo                               0
% 2.30/0.99  fd_cond                                 0
% 2.30/0.99  fd_pseudo_cond                          0
% 2.30/0.99  AC symbols                              1
% 2.30/0.99  
% 2.30/0.99  ------ Input Options Time Limit: Unbounded
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  ------ 
% 2.30/0.99  Current options:
% 2.30/0.99  ------ 
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  ------ Proving...
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  % SZS status Theorem for theBenchmark.p
% 2.30/0.99  
% 2.30/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.30/0.99  
% 2.30/0.99  fof(f7,axiom,(
% 2.30/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f34,plain,(
% 2.30/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f7])).
% 2.30/0.99  
% 2.30/0.99  fof(f6,axiom,(
% 2.30/0.99    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f33,plain,(
% 2.30/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f6])).
% 2.30/0.99  
% 2.30/0.99  fof(f4,axiom,(
% 2.30/0.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f31,plain,(
% 2.30/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f4])).
% 2.30/0.99  
% 2.30/0.99  fof(f19,axiom,(
% 2.30/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f46,plain,(
% 2.30/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f19])).
% 2.30/0.99  
% 2.30/0.99  fof(f51,plain,(
% 2.30/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.30/0.99    inference(definition_unfolding,[],[f33,f31,f46,f46])).
% 2.30/0.99  
% 2.30/0.99  fof(f59,plain,(
% 2.30/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)))) )),
% 2.30/0.99    inference(definition_unfolding,[],[f34,f51,f51])).
% 2.30/0.99  
% 2.30/0.99  fof(f3,axiom,(
% 2.30/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f30,plain,(
% 2.30/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f3])).
% 2.30/0.99  
% 2.30/0.99  fof(f1,axiom,(
% 2.30/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f28,plain,(
% 2.30/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f1])).
% 2.30/0.99  
% 2.30/0.99  fof(f20,axiom,(
% 2.30/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f47,plain,(
% 2.30/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f20])).
% 2.30/0.99  
% 2.30/0.99  fof(f57,plain,(
% 2.30/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.30/0.99    inference(definition_unfolding,[],[f47,f51])).
% 2.30/0.99  
% 2.30/0.99  fof(f9,axiom,(
% 2.30/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f36,plain,(
% 2.30/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)) )),
% 2.30/0.99    inference(cnf_transformation,[],[f9])).
% 2.30/0.99  
% 2.30/0.99  fof(f61,plain,(
% 2.30/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X0)),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X0)))) )),
% 2.30/0.99    inference(definition_unfolding,[],[f36,f51,f51])).
% 2.30/0.99  
% 2.30/0.99  fof(f23,conjecture,(
% 2.30/0.99    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/0.99  
% 2.30/0.99  fof(f24,negated_conjecture,(
% 2.30/0.99    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.30/0.99    inference(negated_conjecture,[],[f23])).
% 2.30/0.99  
% 2.30/0.99  fof(f25,plain,(
% 2.30/0.99    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.30/0.99    inference(ennf_transformation,[],[f24])).
% 2.30/0.99  
% 2.30/0.99  fof(f26,plain,(
% 2.30/0.99    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.30/0.99    introduced(choice_axiom,[])).
% 2.30/0.99  
% 2.30/0.99  fof(f27,plain,(
% 2.30/0.99    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).
% 2.30/0.99  
% 2.30/0.99  fof(f50,plain,(
% 2.30/0.99    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.30/0.99    inference(cnf_transformation,[],[f27])).
% 2.30/0.99  
% 2.30/0.99  fof(f68,plain,(
% 2.30/0.99    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.30/0.99    inference(definition_unfolding,[],[f50,f31,f46,f46])).
% 2.30/0.99  
% 2.30/0.99  cnf(c_54,plain,
% 2.30/0.99      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 2.30/0.99      theory(equality) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_167,plain,
% 2.30/0.99      ( X0_34 != X1_34
% 2.30/0.99      | X0_34 = k1_enumset1(sK0,sK1,sK2)
% 2.30/0.99      | k1_enumset1(sK0,sK1,sK2) != X1_34 ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_54]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_177,plain,
% 2.30/0.99      ( X0_34 = k1_enumset1(sK0,sK1,sK2)
% 2.30/0.99      | X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.30/0.99      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_167]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_263,plain,
% 2.30/0.99      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.30/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 2.30/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_177]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_4,plain,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
% 2.30/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_36,plain,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
% 2.30/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_2,plain,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.30/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1,plain,
% 2.30/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.30/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_43,plain,
% 2.30/0.99      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
% 2.30/0.99      inference(theory_normalisation,[status(thm)],[c_36,c_2,c_1]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_198,plain,
% 2.30/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_0,plain,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.30/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_40,plain,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.30/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_41,plain,
% 2.30/0.99      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.30/0.99      inference(theory_normalisation,[status(thm)],[c_40,c_2,c_1]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_165,plain,
% 2.30/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_41]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_133,plain,
% 2.30/0.99      ( X0_34 != X1_34
% 2.30/0.99      | k1_enumset1(sK0,sK1,sK2) != X1_34
% 2.30/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_54]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_158,plain,
% 2.30/0.99      ( X0_34 != k1_enumset1(sK0,sK1,sK2)
% 2.30/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.30/0.99      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_133]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_164,plain,
% 2.30/0.99      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 2.30/0.99      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.30/0.99      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_158]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_53,plain,( X0_34 = X0_34 ),theory(equality) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_159,plain,
% 2.30/0.99      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(instantiation,[status(thm)],[c_53]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_6,plain,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
% 2.30/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_34,plain,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35))) ),
% 2.30/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_45,plain,
% 2.30/0.99      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X3_35,X3_35,X2_35)))) ),
% 2.30/0.99      inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_13,negated_conjecture,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_27,negated_conjecture,
% 2.30/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_52,negated_conjecture,
% 2.30/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_83,plain,
% 2.30/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK1,sK1,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.30/0.99      inference(demodulation,[status(thm)],[c_45,c_52]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(contradiction,plain,
% 2.30/0.99      ( $false ),
% 2.30/0.99      inference(minisat,
% 2.30/0.99                [status(thm)],
% 2.30/0.99                [c_263,c_198,c_165,c_164,c_159,c_83]) ).
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.30/0.99  
% 2.30/0.99  ------                               Statistics
% 2.30/0.99  
% 2.30/0.99  ------ Selected
% 2.30/0.99  
% 2.30/0.99  total_time:                             0.06
% 2.30/0.99  
%------------------------------------------------------------------------------
