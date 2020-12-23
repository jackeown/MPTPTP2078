%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:24 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 205 expanded)
%              Number of clauses        :   39 (  62 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 238 expanded)
%              Number of equality atoms :   92 ( 237 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f18,f16,f20,f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f17,f16,f20,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f14,f16,f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f15,f16,f16,f16,f16])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f22,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f22,f16,f20,f20])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_17,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k4_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X1_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_14,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k4_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_78,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_17,c_14])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_16,plain,
    ( k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)) = k5_xboole_0(X1_34,k4_xboole_0(X0_34,X1_34)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_79,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k4_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))) = k1_enumset1(X1_36,X2_36,X0_36) ),
    inference(superposition,[status(thm)],[c_17,c_16])).

cnf(c_478,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k4_xboole_0(k1_enumset1(X1_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))) = k1_enumset1(X1_36,X2_36,X0_36) ),
    inference(superposition,[status(thm)],[c_78,c_79])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)),k4_xboole_0(X2_34,k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)))) = k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X1_34,k4_xboole_0(X2_34,X1_34)),X0_34)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_135,plain,
    ( k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X1_34,k4_xboole_0(X2_34,X1_34)),X0_34)) = k5_xboole_0(X2_34,k4_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)),X2_34)) ),
    inference(superposition,[status(thm)],[c_16,c_15])).

cnf(c_497,plain,
    ( k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X1_34,k4_xboole_0(X2_34,X1_34)),X0_34)) = k5_xboole_0(X1_34,k4_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X2_34,X0_34)),X1_34)) ),
    inference(superposition,[status(thm)],[c_16,c_135])).

cnf(c_1375,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)),k4_xboole_0(X2_34,k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)))) = k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X2_34,k4_xboole_0(X1_34,X2_34)),X0_34)) ),
    inference(superposition,[status(thm)],[c_497,c_16])).

cnf(c_2272,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),X0_34)),k4_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k5_xboole_0(X0_34,k4_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),X0_34)))) = k5_xboole_0(X0_34,k4_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),X0_34)) ),
    inference(superposition,[status(thm)],[c_17,c_1375])).

cnf(c_21202,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k4_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k1_enumset1(X0_36,X0_36,X1_36))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X4_36),k4_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X1_36,X4_36))) ),
    inference(superposition,[status(thm)],[c_17,c_2272])).

cnf(c_4,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_21694,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k4_xboole_0(k1_enumset1(sK2,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_21202,c_13])).

cnf(c_22134,plain,
    ( k1_enumset1(sK2,sK0,sK1) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_478,c_21694])).

cnf(c_20,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_64,plain,
    ( X0_34 != X1_34
    | X0_34 = k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) != X1_34 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_229,plain,
    ( X0_34 = k1_enumset1(sK0,sK1,sK2)
    | X0_34 != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_3388,plain,
    ( k1_enumset1(sK2,sK0,sK1) = k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK2,sK0,sK1) != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_18,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_1680,plain,
    ( k1_enumset1(sK2,sK0,sK1) = k1_enumset1(sK2,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_462,plain,
    ( X0_34 != X1_34
    | X0_34 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != X1_34 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_704,plain,
    ( X0_34 != k1_enumset1(sK2,sK0,sK1)
    | X0_34 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_1679,plain,
    ( k1_enumset1(sK2,sK0,sK1) != k1_enumset1(sK2,sK0,sK1)
    | k1_enumset1(sK2,sK0,sK1) = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_705,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(sK2,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_114,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_52,plain,
    ( X0_34 != X1_34
    | k1_enumset1(sK0,sK1,sK2) != X1_34
    | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_95,plain,
    ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)))
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_113,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_62,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_53,plain,
    ( X0_34 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_61,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_54,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22134,c_3388,c_1680,c_1679,c_705,c_114,c_113,c_62,c_61,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.89/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.50  
% 7.89/1.50  ------  iProver source info
% 7.89/1.50  
% 7.89/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.50  git: non_committed_changes: false
% 7.89/1.50  git: last_make_outside_of_git: false
% 7.89/1.50  
% 7.89/1.50  ------ 
% 7.89/1.50  ------ Parsing...
% 7.89/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.89/1.50  ------ Proving...
% 7.89/1.50  ------ Problem Properties 
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  clauses                                 5
% 7.89/1.50  conjectures                             1
% 7.89/1.50  EPR                                     0
% 7.89/1.50  Horn                                    5
% 7.89/1.50  unary                                   5
% 7.89/1.50  binary                                  0
% 7.89/1.50  lits                                    5
% 7.89/1.50  lits eq                                 5
% 7.89/1.50  fd_pure                                 0
% 7.89/1.50  fd_pseudo                               0
% 7.89/1.50  fd_cond                                 0
% 7.89/1.50  fd_pseudo_cond                          0
% 7.89/1.50  AC symbols                              0
% 7.89/1.50  
% 7.89/1.50  ------ Input Options Time Limit: Unbounded
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  ------ 
% 7.89/1.50  Current options:
% 7.89/1.50  ------ 
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  ------ Proving...
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  % SZS status Theorem for theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  fof(f5,axiom,(
% 7.89/1.50    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f18,plain,(
% 7.89/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f5])).
% 7.89/1.50  
% 7.89/1.50  fof(f3,axiom,(
% 7.89/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f16,plain,(
% 7.89/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.89/1.50    inference(cnf_transformation,[],[f3])).
% 7.89/1.50  
% 7.89/1.50  fof(f6,axiom,(
% 7.89/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f19,plain,(
% 7.89/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f6])).
% 7.89/1.50  
% 7.89/1.50  fof(f7,axiom,(
% 7.89/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f20,plain,(
% 7.89/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f7])).
% 7.89/1.50  
% 7.89/1.50  fof(f24,plain,(
% 7.89/1.50    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 7.89/1.50    inference(definition_unfolding,[],[f19,f20])).
% 7.89/1.50  
% 7.89/1.50  fof(f25,plain,(
% 7.89/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2)) )),
% 7.89/1.50    inference(definition_unfolding,[],[f18,f16,f20,f24])).
% 7.89/1.50  
% 7.89/1.50  fof(f8,axiom,(
% 7.89/1.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f21,plain,(
% 7.89/1.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f8])).
% 7.89/1.50  
% 7.89/1.50  fof(f4,axiom,(
% 7.89/1.50    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f17,plain,(
% 7.89/1.50    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f4])).
% 7.89/1.50  
% 7.89/1.50  fof(f23,plain,(
% 7.89/1.50    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.89/1.50    inference(definition_unfolding,[],[f17,f16,f20,f20])).
% 7.89/1.50  
% 7.89/1.50  fof(f28,plain,(
% 7.89/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2)) )),
% 7.89/1.50    inference(definition_unfolding,[],[f21,f23])).
% 7.89/1.50  
% 7.89/1.50  fof(f1,axiom,(
% 7.89/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f14,plain,(
% 7.89/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f1])).
% 7.89/1.50  
% 7.89/1.50  fof(f26,plain,(
% 7.89/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 7.89/1.50    inference(definition_unfolding,[],[f14,f16,f16])).
% 7.89/1.50  
% 7.89/1.50  fof(f2,axiom,(
% 7.89/1.50    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f15,plain,(
% 7.89/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f2])).
% 7.89/1.50  
% 7.89/1.50  fof(f27,plain,(
% 7.89/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 7.89/1.50    inference(definition_unfolding,[],[f15,f16,f16,f16,f16])).
% 7.89/1.50  
% 7.89/1.50  fof(f9,conjecture,(
% 7.89/1.50    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f10,negated_conjecture,(
% 7.89/1.50    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 7.89/1.50    inference(negated_conjecture,[],[f9])).
% 7.89/1.50  
% 7.89/1.50  fof(f11,plain,(
% 7.89/1.50    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 7.89/1.50    inference(ennf_transformation,[],[f10])).
% 7.89/1.50  
% 7.89/1.50  fof(f12,plain,(
% 7.89/1.50    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 7.89/1.50    introduced(choice_axiom,[])).
% 7.89/1.50  
% 7.89/1.50  fof(f13,plain,(
% 7.89/1.50    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 7.89/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 7.89/1.50  
% 7.89/1.50  fof(f22,plain,(
% 7.89/1.50    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 7.89/1.50    inference(cnf_transformation,[],[f13])).
% 7.89/1.50  
% 7.89/1.50  fof(f29,plain,(
% 7.89/1.50    k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 7.89/1.50    inference(definition_unfolding,[],[f22,f16,f20,f20])).
% 7.89/1.50  
% 7.89/1.50  cnf(c_0,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
% 7.89/1.50      inference(cnf_transformation,[],[f25]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_17,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k4_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X1_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_3,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2) ),
% 7.89/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_14,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k4_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_78,plain,
% 7.89/1.50      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_17,c_14]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_1,plain,
% 7.89/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.89/1.50      inference(cnf_transformation,[],[f26]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_16,plain,
% 7.89/1.50      ( k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)) = k5_xboole_0(X1_34,k4_xboole_0(X0_34,X1_34)) ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_79,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k4_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))) = k1_enumset1(X1_36,X2_36,X0_36) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_17,c_16]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_478,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k4_xboole_0(k1_enumset1(X1_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))) = k1_enumset1(X1_36,X2_36,X0_36) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_78,c_79]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_2,plain,
% 7.89/1.50      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 7.89/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_15,plain,
% 7.89/1.50      ( k5_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)),k4_xboole_0(X2_34,k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)))) = k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X1_34,k4_xboole_0(X2_34,X1_34)),X0_34)) ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_135,plain,
% 7.89/1.50      ( k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X1_34,k4_xboole_0(X2_34,X1_34)),X0_34)) = k5_xboole_0(X2_34,k4_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)),X2_34)) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_16,c_15]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_497,plain,
% 7.89/1.50      ( k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X1_34,k4_xboole_0(X2_34,X1_34)),X0_34)) = k5_xboole_0(X1_34,k4_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X2_34,X0_34)),X1_34)) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_16,c_135]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_1375,plain,
% 7.89/1.50      ( k5_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)),k4_xboole_0(X2_34,k5_xboole_0(X0_34,k4_xboole_0(X1_34,X0_34)))) = k5_xboole_0(X0_34,k4_xboole_0(k5_xboole_0(X2_34,k4_xboole_0(X1_34,X2_34)),X0_34)) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_497,c_16]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_2272,plain,
% 7.89/1.50      ( k5_xboole_0(k5_xboole_0(X0_34,k4_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),X0_34)),k4_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k5_xboole_0(X0_34,k4_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),X0_34)))) = k5_xboole_0(X0_34,k4_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),X0_34)) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_17,c_1375]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_21202,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k4_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k1_enumset1(X0_36,X0_36,X1_36))) = k5_xboole_0(k1_enumset1(X0_36,X1_36,X4_36),k4_xboole_0(k1_enumset1(X2_36,X2_36,X3_36),k1_enumset1(X0_36,X1_36,X4_36))) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_17,c_2272]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_4,negated_conjecture,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_13,negated_conjecture,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_21694,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k4_xboole_0(k1_enumset1(sK2,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) != k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_21202,c_13]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_22134,plain,
% 7.89/1.50      ( k1_enumset1(sK2,sK0,sK1) != k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_478,c_21694]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_20,plain,
% 7.89/1.50      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 7.89/1.50      theory(equality) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_64,plain,
% 7.89/1.50      ( X0_34 != X1_34
% 7.89/1.50      | X0_34 = k1_enumset1(sK0,sK1,sK2)
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) != X1_34 ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_229,plain,
% 7.89/1.50      ( X0_34 = k1_enumset1(sK0,sK1,sK2)
% 7.89/1.50      | X0_34 != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_64]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_3388,plain,
% 7.89/1.50      ( k1_enumset1(sK2,sK0,sK1) = k1_enumset1(sK0,sK1,sK2)
% 7.89/1.50      | k1_enumset1(sK2,sK0,sK1) != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_229]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_18,plain,( X0_34 = X0_34 ),theory(equality) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_1680,plain,
% 7.89/1.50      ( k1_enumset1(sK2,sK0,sK1) = k1_enumset1(sK2,sK0,sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_462,plain,
% 7.89/1.50      ( X0_34 != X1_34
% 7.89/1.50      | X0_34 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
% 7.89/1.50      | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != X1_34 ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_704,plain,
% 7.89/1.50      ( X0_34 != k1_enumset1(sK2,sK0,sK1)
% 7.89/1.50      | X0_34 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
% 7.89/1.50      | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK0,sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_462]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_1679,plain,
% 7.89/1.50      ( k1_enumset1(sK2,sK0,sK1) != k1_enumset1(sK2,sK0,sK1)
% 7.89/1.50      | k1_enumset1(sK2,sK0,sK1) = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
% 7.89/1.50      | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK0,sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_704]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_705,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(sK2,sK0,sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_114,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_52,plain,
% 7.89/1.50      ( X0_34 != X1_34
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) != X1_34
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_95,plain,
% 7.89/1.50      ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)))
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_52]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_113,plain,
% 7.89/1.50      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)))
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)))
% 7.89/1.50      | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_95]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_62,plain,
% 7.89/1.50      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) = k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_53,plain,
% 7.89/1.50      ( X0_34 != k1_enumset1(sK0,sK1,sK2)
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_52]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_61,plain,
% 7.89/1.50      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 7.89/1.50      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)))
% 7.89/1.50      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) != k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_53]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_54,plain,
% 7.89/1.50      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(contradiction,plain,
% 7.89/1.50      ( $false ),
% 7.89/1.50      inference(minisat,
% 7.89/1.50                [status(thm)],
% 7.89/1.50                [c_22134,c_3388,c_1680,c_1679,c_705,c_114,c_113,c_62,
% 7.89/1.50                 c_61,c_54]) ).
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  ------                               Statistics
% 7.89/1.50  
% 7.89/1.50  ------ Selected
% 7.89/1.50  
% 7.89/1.50  total_time:                             0.939
% 7.89/1.50  
%------------------------------------------------------------------------------
