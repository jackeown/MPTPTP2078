%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:29 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
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
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
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

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f32,f43,f43])).

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

cnf(c_94,plain,
    ( k1_enumset1(sK0,sK1,sK2) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_1850,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_33,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_40,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1])).

cnf(c_738,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_114,plain,
    ( X0_34 != X1_34
    | k1_enumset1(sK0,sK1,sK2) != X1_34
    | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_264,plain,
    ( X0_34 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_737,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_34,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_39,plain,
    ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1])).

cnf(c_228,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_32,c_2,c_1])).

cnf(c_170,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_152,plain,
    ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_169,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_46,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1850,c_738,c_737,c_228,c_170,c_169,c_146,c_145,c_116,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.67/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.99  
% 2.67/0.99  ------  iProver source info
% 2.67/0.99  
% 2.67/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.99  git: non_committed_changes: false
% 2.67/0.99  git: last_make_outside_of_git: false
% 2.67/0.99  
% 2.67/0.99  ------ 
% 2.67/0.99  ------ Parsing...
% 2.67/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.67/0.99  ------ Proving...
% 2.67/0.99  ------ Problem Properties 
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  clauses                                 11
% 2.67/0.99  conjectures                             1
% 2.67/0.99  EPR                                     0
% 2.67/0.99  Horn                                    11
% 2.67/0.99  unary                                   11
% 2.67/0.99  binary                                  0
% 2.67/0.99  lits                                    11
% 2.67/0.99  lits eq                                 11
% 2.67/0.99  fd_pure                                 0
% 2.67/0.99  fd_pseudo                               0
% 2.67/0.99  fd_cond                                 0
% 2.67/0.99  fd_pseudo_cond                          0
% 2.67/0.99  AC symbols                              1
% 2.67/0.99  
% 2.67/0.99  ------ Input Options Time Limit: Unbounded
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  ------ 
% 2.67/0.99  Current options:
% 2.67/0.99  ------ 
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  ------ Proving...
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS status Theorem for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  fof(f8,axiom,(
% 2.67/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f31,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f8])).
% 2.67/0.99  
% 2.67/0.99  fof(f6,axiom,(
% 2.67/0.99    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f29,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f6])).
% 2.67/0.99  
% 2.67/0.99  fof(f4,axiom,(
% 2.67/0.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f27,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f4])).
% 2.67/0.99  
% 2.67/0.99  fof(f16,axiom,(
% 2.67/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f39,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f16])).
% 2.67/0.99  
% 2.67/0.99  fof(f43,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.67/0.99    inference(definition_unfolding,[],[f29,f27,f39,f39])).
% 2.67/0.99  
% 2.67/0.99  fof(f49,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)))) )),
% 2.67/0.99    inference(definition_unfolding,[],[f31,f43,f43])).
% 2.67/0.99  
% 2.67/0.99  fof(f3,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f26,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f3])).
% 2.67/0.99  
% 2.67/0.99  fof(f1,axiom,(
% 2.67/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f24,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f1])).
% 2.67/0.99  
% 2.67/0.99  fof(f5,axiom,(
% 2.67/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f28,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f5])).
% 2.67/0.99  
% 2.67/0.99  fof(f2,axiom,(
% 2.67/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f25,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f2])).
% 2.67/0.99  
% 2.67/0.99  fof(f48,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.67/0.99    inference(definition_unfolding,[],[f28,f25,f27])).
% 2.67/0.99  
% 2.67/0.99  fof(f9,axiom,(
% 2.67/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f32,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f9])).
% 2.67/0.99  
% 2.67/0.99  fof(f50,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)))) )),
% 2.67/0.99    inference(definition_unfolding,[],[f32,f43,f43])).
% 2.67/0.99  
% 2.67/0.99  fof(f17,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f40,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f17])).
% 2.67/0.99  
% 2.67/0.99  fof(f47,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.67/0.99    inference(definition_unfolding,[],[f40,f43])).
% 2.67/0.99  
% 2.67/0.99  fof(f19,conjecture,(
% 2.67/0.99    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f20,negated_conjecture,(
% 2.67/0.99    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.67/0.99    inference(negated_conjecture,[],[f19])).
% 2.67/0.99  
% 2.67/0.99  fof(f21,plain,(
% 2.67/0.99    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.67/0.99    inference(ennf_transformation,[],[f20])).
% 2.67/0.99  
% 2.67/0.99  fof(f22,plain,(
% 2.67/0.99    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.67/0.99    introduced(choice_axiom,[])).
% 2.67/0.99  
% 2.67/0.99  fof(f23,plain,(
% 2.67/0.99    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 2.67/0.99  
% 2.67/0.99  fof(f42,plain,(
% 2.67/0.99    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f23])).
% 2.67/0.99  
% 2.67/0.99  fof(f56,plain,(
% 2.67/0.99    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.67/0.99    inference(definition_unfolding,[],[f42,f27,f39,f39])).
% 2.67/0.99  
% 2.67/0.99  cnf(c_48,plain,
% 2.67/0.99      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 2.67/0.99      theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_94,plain,
% 2.67/0.99      ( k1_enumset1(sK0,sK1,sK2) != X0_34
% 2.67/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
% 2.67/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_48]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1850,plain,
% 2.67/0.99      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.67/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 2.67/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_94]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
% 2.67/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_33,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1,plain,
% 2.67/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_40,plain,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
% 2.67/0.99      inference(theory_normalisation,[status(thm)],[c_33,c_2,c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_738,plain,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_40]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_114,plain,
% 2.67/0.99      ( X0_34 != X1_34
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) != X1_34
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_48]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_264,plain,
% 2.67/0.99      ( X0_34 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_114]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_737,plain,
% 2.67/0.99      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.67/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_264]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.67/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_34,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_39,plain,
% 2.67/0.99      ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 2.67/0.99      inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_228,plain,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_39]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
% 2.67/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_32,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_41,plain,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
% 2.67/0.99      inference(theory_normalisation,[status(thm)],[c_32,c_2,c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_170,plain,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_41]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_152,plain,
% 2.67/0.99      ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_114]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_169,plain,
% 2.67/0.99      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.67/0.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_152]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_0,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_37,plain,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_38,plain,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.67/0.99      inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_146,plain,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_38]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_115,plain,
% 2.67/0.99      ( X0_34 != k1_enumset1(sK0,sK1,sK2)
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_114]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_145,plain,
% 2.67/0.99      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 2.67/0.99      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.67/0.99      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_115]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_47,plain,( X0_34 = X0_34 ),theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_116,plain,
% 2.67/0.99      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_47]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_11,negated_conjecture,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_27,negated_conjecture,
% 2.67/0.99      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_46,negated_conjecture,
% 2.67/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.67/0.99      inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(contradiction,plain,
% 2.67/0.99      ( $false ),
% 2.67/0.99      inference(minisat,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_1850,c_738,c_737,c_228,c_170,c_169,c_146,c_145,c_116,
% 2.67/0.99                 c_46]) ).
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  ------                               Statistics
% 2.67/0.99  
% 2.67/0.99  ------ Selected
% 2.67/0.99  
% 2.67/0.99  total_time:                             0.136
% 2.67/0.99  
%------------------------------------------------------------------------------
