%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:28 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 120 expanded)
%              Number of clauses        :   25 (  37 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 143 expanded)
%              Number of equality atoms :   65 ( 142 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f10])).

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

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0)),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0))) ),
    inference(definition_unfolding,[],[f33,f43,f43])).

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

cnf(c_468,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X1),k1_enumset1(X0,X0,X2)),k3_xboole_0(k1_enumset1(X3,X3,X1),k1_enumset1(X0,X0,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_31,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X1_35),k1_enumset1(X0_35,X0_35,X2_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X1_35),k1_enumset1(X0_35,X0_35,X2_35))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_42,plain,
    ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X3_35,X3_35,X0_35)))) ),
    inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1])).

cnf(c_233,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_172,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
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
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1))))
    | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
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
    inference(minisat,[status(thm)],[c_468,c_233,c_172,c_171,c_146,c_145,c_116,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.26/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.02  
% 2.26/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.26/1.02  
% 2.26/1.02  ------  iProver source info
% 2.26/1.02  
% 2.26/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.26/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.26/1.02  git: non_committed_changes: false
% 2.26/1.02  git: last_make_outside_of_git: false
% 2.26/1.02  
% 2.26/1.02  ------ 
% 2.26/1.02  ------ Parsing...
% 2.26/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.26/1.02  
% 2.26/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.26/1.02  
% 2.26/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.26/1.02  
% 2.26/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.26/1.02  ------ Proving...
% 2.26/1.02  ------ Problem Properties 
% 2.26/1.02  
% 2.26/1.02  
% 2.26/1.02  clauses                                 11
% 2.26/1.02  conjectures                             1
% 2.26/1.02  EPR                                     0
% 2.26/1.02  Horn                                    11
% 2.26/1.02  unary                                   11
% 2.26/1.02  binary                                  0
% 2.26/1.02  lits                                    11
% 2.26/1.02  lits eq                                 11
% 2.26/1.02  fd_pure                                 0
% 2.26/1.02  fd_pseudo                               0
% 2.26/1.02  fd_cond                                 0
% 2.26/1.02  fd_pseudo_cond                          0
% 2.26/1.02  AC symbols                              1
% 2.26/1.02  
% 2.26/1.02  ------ Input Options Time Limit: Unbounded
% 2.26/1.02  
% 2.26/1.02  
% 2.26/1.02  ------ 
% 2.26/1.02  Current options:
% 2.26/1.02  ------ 
% 2.26/1.02  
% 2.26/1.02  
% 2.26/1.02  
% 2.26/1.02  
% 2.26/1.02  ------ Proving...
% 2.26/1.02  
% 2.26/1.02  
% 2.26/1.02  % SZS status Theorem for theBenchmark.p
% 2.26/1.02  
% 2.26/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.26/1.02  
% 2.26/1.02  fof(f10,axiom,(
% 2.26/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f33,plain,(
% 2.26/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)) )),
% 2.26/1.02    inference(cnf_transformation,[],[f10])).
% 2.26/1.02  
% 2.26/1.02  fof(f6,axiom,(
% 2.26/1.02    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f29,plain,(
% 2.26/1.02    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.26/1.02    inference(cnf_transformation,[],[f6])).
% 2.26/1.02  
% 2.26/1.02  fof(f4,axiom,(
% 2.26/1.02    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f27,plain,(
% 2.26/1.02    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.26/1.02    inference(cnf_transformation,[],[f4])).
% 2.26/1.02  
% 2.26/1.02  fof(f16,axiom,(
% 2.26/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f39,plain,(
% 2.26/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.26/1.02    inference(cnf_transformation,[],[f16])).
% 2.26/1.02  
% 2.26/1.02  fof(f43,plain,(
% 2.26/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.26/1.02    inference(definition_unfolding,[],[f29,f27,f39,f39])).
% 2.26/1.02  
% 2.26/1.02  fof(f51,plain,(
% 2.26/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0)),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X3,X3,X0)))) )),
% 2.26/1.02    inference(definition_unfolding,[],[f33,f43,f43])).
% 2.26/1.02  
% 2.26/1.02  fof(f3,axiom,(
% 2.26/1.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f26,plain,(
% 2.26/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.26/1.02    inference(cnf_transformation,[],[f3])).
% 2.26/1.02  
% 2.26/1.02  fof(f1,axiom,(
% 2.26/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f24,plain,(
% 2.26/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.26/1.02    inference(cnf_transformation,[],[f1])).
% 2.26/1.02  
% 2.26/1.02  fof(f17,axiom,(
% 2.26/1.02    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f40,plain,(
% 2.26/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.26/1.02    inference(cnf_transformation,[],[f17])).
% 2.26/1.02  
% 2.26/1.02  fof(f47,plain,(
% 2.26/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2)) )),
% 2.26/1.02    inference(definition_unfolding,[],[f40,f43])).
% 2.26/1.02  
% 2.26/1.02  fof(f19,conjecture,(
% 2.26/1.02    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.26/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.02  
% 2.26/1.02  fof(f20,negated_conjecture,(
% 2.26/1.02    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.26/1.02    inference(negated_conjecture,[],[f19])).
% 2.26/1.02  
% 2.26/1.02  fof(f21,plain,(
% 2.26/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.26/1.02    inference(ennf_transformation,[],[f20])).
% 2.26/1.02  
% 2.26/1.02  fof(f22,plain,(
% 2.26/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.26/1.02    introduced(choice_axiom,[])).
% 2.26/1.02  
% 2.26/1.02  fof(f23,plain,(
% 2.26/1.02    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.26/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 2.26/1.02  
% 2.26/1.02  fof(f42,plain,(
% 2.26/1.02    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.26/1.02    inference(cnf_transformation,[],[f23])).
% 2.26/1.02  
% 2.26/1.02  fof(f56,plain,(
% 2.26/1.02    k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2)),
% 2.26/1.02    inference(definition_unfolding,[],[f42,f27,f39,f39])).
% 2.26/1.02  
% 2.26/1.02  cnf(c_48,plain,
% 2.26/1.02      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 2.26/1.02      theory(equality) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_94,plain,
% 2.26/1.02      ( k1_enumset1(sK0,sK1,sK2) != X0_34
% 2.26/1.02      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != X0_34
% 2.26/1.02      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_48]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_468,plain,
% 2.26/1.02      ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1))))
% 2.26/1.02      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k1_enumset1(sK0,sK1,sK2)
% 2.26/1.02      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_94]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_6,plain,
% 2.26/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)),k3_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X1),k1_enumset1(X0,X0,X2)),k3_xboole_0(k1_enumset1(X3,X3,X1),k1_enumset1(X0,X0,X2))) ),
% 2.26/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_31,plain,
% 2.26/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3_35,X3_35,X1_35),k1_enumset1(X0_35,X0_35,X2_35)),k3_xboole_0(k1_enumset1(X3_35,X3_35,X1_35),k1_enumset1(X0_35,X0_35,X2_35))) ),
% 2.26/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_2,plain,
% 2.26/1.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.26/1.02      inference(cnf_transformation,[],[f26]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_1,plain,
% 2.26/1.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.26/1.02      inference(cnf_transformation,[],[f24]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_42,plain,
% 2.26/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k5_xboole_0(k1_enumset1(X2_35,X2_35,X3_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X1_35),k1_enumset1(X2_35,X2_35,X3_35)))) = k5_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k5_xboole_0(k1_enumset1(X3_35,X3_35,X0_35),k3_xboole_0(k1_enumset1(X2_35,X2_35,X1_35),k1_enumset1(X3_35,X3_35,X0_35)))) ),
% 2.26/1.02      inference(theory_normalisation,[status(thm)],[c_31,c_2,c_1]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_233,plain,
% 2.26/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_42]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_172,plain,
% 2.26/1.02      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_42]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_114,plain,
% 2.26/1.02      ( X0_34 != X1_34
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) != X1_34
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) = X0_34 ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_48]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_152,plain,
% 2.26/1.02      ( X0_34 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_114]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_171,plain,
% 2.26/1.02      ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1))))
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.26/1.02      | k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_152]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_0,plain,
% 2.26/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 2.26/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_37,plain,
% 2.26/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.26/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_38,plain,
% 2.26/1.02      ( k5_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k5_xboole_0(k1_enumset1(X1_35,X1_35,X2_35),k3_xboole_0(k1_enumset1(X0_35,X0_35,X0_35),k1_enumset1(X1_35,X1_35,X2_35)))) = k1_enumset1(X0_35,X1_35,X2_35) ),
% 2.26/1.02      inference(theory_normalisation,[status(thm)],[c_37,c_2,c_1]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_146,plain,
% 2.26/1.02      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) = k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_38]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_115,plain,
% 2.26/1.02      ( X0_34 != k1_enumset1(sK0,sK1,sK2)
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) = X0_34
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_114]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_145,plain,
% 2.26/1.02      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
% 2.26/1.02      | k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))))
% 2.26/1.02      | k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_115]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_47,plain,( X0_34 = X0_34 ),theory(equality) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_116,plain,
% 2.26/1.02      ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(instantiation,[status(thm)],[c_47]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_11,negated_conjecture,
% 2.26/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_27,negated_conjecture,
% 2.26/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(c_46,negated_conjecture,
% 2.26/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)))) != k1_enumset1(sK0,sK1,sK2) ),
% 2.26/1.02      inference(theory_normalisation,[status(thm)],[c_27,c_2,c_1]) ).
% 2.26/1.02  
% 2.26/1.02  cnf(contradiction,plain,
% 2.26/1.02      ( $false ),
% 2.26/1.02      inference(minisat,
% 2.26/1.02                [status(thm)],
% 2.26/1.02                [c_468,c_233,c_172,c_171,c_146,c_145,c_116,c_46]) ).
% 2.26/1.02  
% 2.26/1.02  
% 2.26/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.26/1.02  
% 2.26/1.02  ------                               Statistics
% 2.26/1.02  
% 2.26/1.02  ------ Selected
% 2.26/1.02  
% 2.26/1.02  total_time:                             0.108
% 2.26/1.02  
%------------------------------------------------------------------------------
