%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:28 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 106 expanded)
%              Number of clauses        :   28 (  37 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 129 expanded)
%              Number of equality atoms :   73 ( 128 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f29,f27,f39,f39])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X2),k1_enumset1(X3,X3,X1)),k3_xboole_0(k1_enumset1(X0,X0,X2),k1_enumset1(X3,X3,X1))) ),
    inference(definition_unfolding,[],[f31,f43,f43])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f28,f25,f27])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f19,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f42,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f42,f27,f39,f39])).

cnf(c_48,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_97,plain,
    ( k1_enumset1(sK0,sK1,sK2) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_240,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_33,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X1_35,X1_35,X2_35))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_40,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k1_enumset1(X3_35,X3_35,X1_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1])).

cnf(c_214,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_34,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_39,plain,
    ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1])).

cnf(c_171,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_117,plain,
    ( X0_34 != X1_34
    | k1_enumset1(sK0,sK1,sK2) != X1_34
    | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_155,plain,
    ( X0_34 != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_170,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_37,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_38,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
    inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1])).

cnf(c_149,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_118,plain,
    ( X0_34 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_148,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_47,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_119,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_46,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_240,c_214,c_171,c_170,c_149,c_148,c_119,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:13:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.45/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/0.98  
% 2.45/0.98  ------  iProver source info
% 2.45/0.98  
% 2.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/0.98  git: non_committed_changes: false
% 2.45/0.98  git: last_make_outside_of_git: false
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  ------ Parsing...
% 2.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.45/0.98  ------ Proving...
% 2.45/0.98  ------ Problem Properties 
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  clauses                                 11
% 2.45/0.98  conjectures                             1
% 2.45/0.98  EPR                                     0
% 2.45/0.98  Horn                                    11
% 2.45/0.98  unary                                   11
% 2.45/0.98  binary                                  0
% 2.45/0.98  lits                                    11
% 2.45/0.98  lits eq                                 11
% 2.45/0.98  fd_pure                                 0
% 2.45/0.98  fd_pseudo                               0
% 2.45/0.98  fd_cond                                 0
% 2.45/0.98  fd_pseudo_cond                          0
% 2.45/0.98  AC symbols                              1
% 2.45/0.98  
% 2.45/0.98  ------ Input Options Time Limit: Unbounded
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  Current options:
% 2.45/0.98  ------ 
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ Proving...
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  % SZS status Theorem for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  fof(f8,axiom,(
% 2.45/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f31,plain,(
% 2.45/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f8])).
% 2.45/0.98  
% 2.45/0.98  fof(f6,axiom,(
% 2.45/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f29,plain,(
% 2.45/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f6])).
% 2.45/0.98  
% 2.45/0.98  fof(f4,axiom,(
% 2.45/0.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f27,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f4])).
% 2.45/0.98  
% 2.45/0.98  fof(f16,axiom,(
% 2.45/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f39,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f16])).
% 2.45/0.98  
% 2.45/0.98  fof(f43,plain,(
% 2.45/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.45/0.98    inference(definition_unfolding,[],[f29,f27,f39,f39])).
% 2.45/0.98  
% 2.45/0.98  fof(f49,plain,(
% 2.45/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X2),k1_enumset1(X3,X3,X1)),k3_xboole_0(k1_enumset1(X0,X0,X2),k1_enumset1(X3,X3,X1)))) )),
% 2.45/0.98    inference(definition_unfolding,[],[f31,f43,f43])).
% 2.45/0.98  
% 2.45/0.98  fof(f3,axiom,(
% 2.45/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f26,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f3])).
% 2.45/0.98  
% 2.45/0.98  fof(f1,axiom,(
% 2.45/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f24,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f1])).
% 2.45/0.98  
% 2.45/0.98  fof(f5,axiom,(
% 2.45/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f28,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f5])).
% 2.45/0.98  
% 2.45/0.98  fof(f2,axiom,(
% 2.45/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f25,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f2])).
% 2.45/0.98  
% 2.45/0.98  fof(f48,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.45/0.98    inference(definition_unfolding,[],[f28,f25,f27])).
% 2.45/0.98  
% 2.45/0.98  fof(f17,axiom,(
% 2.45/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f40,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f17])).
% 2.45/0.98  
% 2.45/0.98  fof(f47,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.45/0.98    inference(definition_unfolding,[],[f40,f43])).
% 2.45/0.98  
% 2.45/0.98  fof(f19,conjecture,(
% 2.45/0.98    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f20,negated_conjecture,(
% 2.45/0.98    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.45/0.98    inference(negated_conjecture,[],[f19])).
% 2.45/0.98  
% 2.45/0.98  fof(f21,plain,(
% 2.45/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.45/0.98    inference(ennf_transformation,[],[f20])).
% 2.45/0.98  
% 2.45/0.98  fof(f22,plain,(
% 2.45/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f23,plain,(
% 2.45/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 2.45/0.98  
% 2.45/0.98  fof(f42,plain,(
% 2.45/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.45/0.98    inference(cnf_transformation,[],[f23])).
% 2.45/0.98  
% 2.45/0.98  fof(f56,plain,(
% 2.45/0.98    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.45/0.98    inference(definition_unfolding,[],[f42,f27,f39,f39])).
% 2.45/0.98  
% 2.45/0.98  cnf(c_48,plain,
% 2.45/0.98      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 2.45/0.98      theory(equality) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_97,plain,
% 2.45/0.98      ( k1_enumset1(sK0,sK1,sK2) != X0_34
% 2.45/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
% 2.45/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_48]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_240,plain,
% 2.45/0.98      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))
% 2.45/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 2.45/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_97]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_4,plain,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2))) ),
% 2.45/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_33,plain,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X1_35,X1_35,X2_35))) ),
% 2.45/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2,plain,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.45/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1,plain,
% 2.45/0.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_40,plain,
% 2.45/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X1_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X2_35),k1_enumset1(X3_35,X3_35,X1_35)))) ),
% 2.45/0.98      inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_214,plain,
% 2.45/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_40]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3,plain,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.45/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_34,plain,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 2.45/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_39,plain,
% 2.45/0.98      ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 2.45/0.98      inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_171,plain,
% 2.45/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_39]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_117,plain,
% 2.45/0.98      ( X0_34 != X1_34
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) != X1_34
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_48]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_155,plain,
% 2.45/0.98      ( X0_34 != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_117]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_170,plain,
% 2.45/0.98      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))
% 2.45/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_155]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_0,plain,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.45/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_37,plain,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.45/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_38,plain,
% 2.45/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X2_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k1_enumset1(X2_35,X0_35,X1_35) ),
% 2.45/0.98      inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_149,plain,
% 2.45/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_38]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_118,plain,
% 2.45/0.98      ( X0_34 != k1_enumset1(sK0,sK1,sK2)
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_117]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_148,plain,
% 2.45/0.98      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 2.45/0.98      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.45/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_118]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_47,plain,( X0_34 = X0_34 ),theory(equality) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_119,plain,
% 2.45/0.98      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_47]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_11,negated_conjecture,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_27,negated_conjecture,
% 2.45/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_46,negated_conjecture,
% 2.45/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.45/0.98      inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(contradiction,plain,
% 2.45/0.98      ( $false ),
% 2.45/0.98      inference(minisat,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_240,c_214,c_171,c_170,c_149,c_148,c_119,c_46]) ).
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  ------                               Statistics
% 2.45/0.98  
% 2.45/0.98  ------ Selected
% 2.45/0.98  
% 2.45/0.98  total_time:                             0.055
% 2.45/0.98  
%------------------------------------------------------------------------------
