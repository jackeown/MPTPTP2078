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
% DateTime   : Thu Dec  3 11:28:29 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
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

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f28,f40,f40])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(definition_unfolding,[],[f32,f45,f45])).

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

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f29,f26,f28])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f33,f45,f45])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f45])).

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
    inference(definition_unfolding,[],[f44,f28,f40,f40])).

cnf(c_46,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_97,plain,
    ( k1_enumset1(sK0,sK1,sK2) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_2334,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_38,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1])).

cnf(c_993,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_117,plain,
    ( X0_34 != X1_34
    | k1_enumset1(sK0,sK1,sK2) != X1_34
    | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_475,plain,
    ( X0_34 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_992,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_31,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_36,plain,
    ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
    inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1])).

cnf(c_236,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_39,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_28,c_2,c_1])).

cnf(c_175,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_155,plain,
    ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_174,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_35,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
    inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1])).

cnf(c_149,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_118,plain,
    ( X0_34 != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = X0_34
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_148,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_45,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_119,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_44,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_23,c_2,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2334,c_993,c_992,c_236,c_175,c_174,c_149,c_148,c_119,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.59/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/0.98  
% 2.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.98  
% 2.59/0.98  ------  iProver source info
% 2.59/0.98  
% 2.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.98  git: non_committed_changes: false
% 2.59/0.98  git: last_make_outside_of_git: false
% 2.59/0.98  
% 2.59/0.98  ------ 
% 2.59/0.98  ------ Parsing...
% 2.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.59/0.98  ------ Proving...
% 2.59/0.98  ------ Problem Properties 
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  clauses                                 12
% 2.59/0.98  conjectures                             1
% 2.59/0.98  EPR                                     0
% 2.59/0.98  Horn                                    12
% 2.59/0.98  unary                                   12
% 2.59/0.98  binary                                  0
% 2.59/0.98  lits                                    12
% 2.59/0.98  lits eq                                 12
% 2.59/0.98  fd_pure                                 0
% 2.59/0.98  fd_pseudo                               0
% 2.59/0.98  fd_cond                                 0
% 2.59/0.98  fd_pseudo_cond                          0
% 2.59/0.98  AC symbols                              1
% 2.59/0.98  
% 2.59/0.98  ------ Input Options Time Limit: Unbounded
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  ------ 
% 2.59/0.98  Current options:
% 2.59/0.98  ------ 
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  ------ Proving...
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  % SZS status Theorem for theBenchmark.p
% 2.59/0.98  
% 2.59/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.98  
% 2.59/0.98  fof(f8,axiom,(
% 2.59/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f32,plain,(
% 2.59/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f8])).
% 2.59/0.98  
% 2.59/0.98  fof(f6,axiom,(
% 2.59/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f30,plain,(
% 2.59/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f6])).
% 2.59/0.98  
% 2.59/0.98  fof(f4,axiom,(
% 2.59/0.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f28,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f4])).
% 2.59/0.98  
% 2.59/0.98  fof(f16,axiom,(
% 2.59/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f40,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f16])).
% 2.59/0.98  
% 2.59/0.98  fof(f45,plain,(
% 2.59/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.59/0.98    inference(definition_unfolding,[],[f30,f28,f40,f40])).
% 2.59/0.98  
% 2.59/0.98  fof(f53,plain,(
% 2.59/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)))) )),
% 2.59/0.98    inference(definition_unfolding,[],[f32,f45,f45])).
% 2.59/0.98  
% 2.59/0.98  fof(f3,axiom,(
% 2.59/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f27,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f3])).
% 2.59/0.98  
% 2.59/0.98  fof(f1,axiom,(
% 2.59/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f25,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f1])).
% 2.59/0.98  
% 2.59/0.98  fof(f5,axiom,(
% 2.59/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f29,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f5])).
% 2.59/0.98  
% 2.59/0.98  fof(f2,axiom,(
% 2.59/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f26,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f2])).
% 2.59/0.98  
% 2.59/0.98  fof(f51,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.59/0.98    inference(definition_unfolding,[],[f29,f26,f28])).
% 2.59/0.98  
% 2.59/0.98  fof(f9,axiom,(
% 2.59/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f33,plain,(
% 2.59/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f9])).
% 2.59/0.98  
% 2.59/0.98  fof(f54,plain,(
% 2.59/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)),k3_xboole_0(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X0)))) )),
% 2.59/0.98    inference(definition_unfolding,[],[f33,f45,f45])).
% 2.59/0.98  
% 2.59/0.98  fof(f17,axiom,(
% 2.59/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f41,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f17])).
% 2.59/0.98  
% 2.59/0.98  fof(f50,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.59/0.98    inference(definition_unfolding,[],[f41,f45])).
% 2.59/0.98  
% 2.59/0.98  fof(f20,conjecture,(
% 2.59/0.98    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f21,negated_conjecture,(
% 2.59/0.98    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.59/0.98    inference(negated_conjecture,[],[f20])).
% 2.59/0.98  
% 2.59/0.98  fof(f22,plain,(
% 2.59/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.59/0.98    inference(ennf_transformation,[],[f21])).
% 2.59/0.98  
% 2.59/0.98  fof(f23,plain,(
% 2.59/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f24,plain,(
% 2.59/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 2.59/0.98  
% 2.59/0.98  fof(f44,plain,(
% 2.59/0.98    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.59/0.98    inference(cnf_transformation,[],[f24])).
% 2.59/0.98  
% 2.59/0.98  fof(f59,plain,(
% 2.59/0.98    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.59/0.98    inference(definition_unfolding,[],[f44,f28,f40,f40])).
% 2.59/0.98  
% 2.59/0.98  cnf(c_46,plain,
% 2.59/0.98      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 2.59/0.98      theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_97,plain,
% 2.59/0.98      ( k1_enumset1(sK0,sK1,sK2) != X0_34
% 2.59/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
% 2.59/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_46]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2334,plain,
% 2.59/0.98      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.59/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 2.59/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_97]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X0,X0,X3),k1_enumset1(X2,X2,X1))) ),
% 2.59/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_29,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
% 2.59/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.59/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1,plain,
% 2.59/0.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_38,plain,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k1_enumset1(X0_35,X0_35,X1_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X0_35,X0_35,X3_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X0_35,X0_35,X3_35)))) ),
% 2.59/0.98      inference(theory_normalisation,[status(thm)],[c_29,c_2,c_1]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_993,plain,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_38]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_117,plain,
% 2.59/0.98      ( X0_34 != X1_34
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) != X1_34
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_46]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_475,plain,
% 2.59/0.98      ( X0_34 != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_117]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_992,plain,
% 2.59/0.98      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.59/0.98      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_475]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.59/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_31,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),k3_xboole_0(X0_34,X1_34)) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 2.59/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_36,plain,
% 2.59/0.98      ( k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X0_34,X1_34))) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,k3_xboole_0(X1_34,X0_34))) ),
% 2.59/0.98      inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_236,plain,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_36]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_6,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1)),k3_xboole_0(k1_enumset1(X3,X3,X0),k1_enumset1(X2,X2,X1))) ),
% 2.59/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_28,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k1_enumset1(X2_35,X2_35,X1_35))) ),
% 2.59/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_39,plain,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X0_35),k3_xboole_0(k1_enumset1(X1_35,X1_35,X3_35),k1_enumset1(X2_35,X2_35,X0_35)))) ),
% 2.59/0.98      inference(theory_normalisation,[status(thm)],[c_28,c_2,c_1]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_175,plain,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_39]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_155,plain,
% 2.59/0.98      ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_117]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_174,plain,
% 2.59/0.98      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))))
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.59/0.98      | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_155]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_0,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.59/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_34,plain,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.59/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_35,plain,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.59/0.98      inference(theory_normalisation,[status(thm)],[c_34,c_2,c_1]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_149,plain,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_35]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_118,plain,
% 2.59/0.98      ( X0_34 != k1_enumset1(sK0,sK1,sK2)
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_117]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_148,plain,
% 2.59/0.98      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 2.59/0.98      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.59/0.98      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_118]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_45,plain,( X0_34 = X0_34 ),theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_119,plain,
% 2.59/0.98      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_45]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_11,negated_conjecture,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_23,negated_conjecture,
% 2.59/0.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_44,negated_conjecture,
% 2.59/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.59/0.98      inference(theory_normalisation,[status(thm)],[c_23,c_2,c_1]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(contradiction,plain,
% 2.59/0.98      ( $false ),
% 2.59/0.98      inference(minisat,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_2334,c_993,c_992,c_236,c_175,c_174,c_149,c_148,c_119,
% 2.59/0.98                 c_44]) ).
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/0.98  
% 2.59/0.98  ------                               Statistics
% 2.59/0.98  
% 2.59/0.98  ------ Selected
% 2.59/0.98  
% 2.59/0.98  total_time:                             0.192
% 2.59/0.98  
%------------------------------------------------------------------------------
