%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:55 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 188 expanded)
%              Number of clauses        :   24 (  29 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 ( 205 expanded)
%              Number of equality atoms :   79 ( 204 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f45,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f34,f44])).

fof(f46,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f28,f41,f38,f46])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f25,f44,f44])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f40,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f40,f43,f43])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f27,f43,f43])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f26,f43,f43])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k3_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_312,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X2_36,X0_36,X3_36) ),
    inference(superposition,[status(thm)],[c_24,c_25])).

cnf(c_13228,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
    inference(superposition,[status(thm)],[c_25,c_312])).

cnf(c_8,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_13960,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_13228,c_17])).

cnf(c_27,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_188,plain,
    ( X0_35 != X1_35
    | X0_35 = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != X1_35 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_886,plain,
    ( X0_35 != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
    | X0_35 = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_2513,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_3,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1404,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X3_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_162,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_71,plain,
    ( X0_35 != X1_35
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != X1_35
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = X0_35 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_133,plain,
    ( X0_35 != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = X0_35
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_161,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_66,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13960,c_2513,c_1404,c_162,c_161,c_66])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.01/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.98  
% 4.01/0.98  ------  iProver source info
% 4.01/0.98  
% 4.01/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.98  git: non_committed_changes: false
% 4.01/0.98  git: last_make_outside_of_git: false
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  ------ Parsing...
% 4.01/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.01/0.98  ------ Proving...
% 4.01/0.98  ------ Problem Properties 
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  clauses                                 9
% 4.01/0.98  conjectures                             1
% 4.01/0.98  EPR                                     0
% 4.01/0.98  Horn                                    9
% 4.01/0.98  unary                                   9
% 4.01/0.98  binary                                  0
% 4.01/0.98  lits                                    9
% 4.01/0.98  lits eq                                 9
% 4.01/0.98  fd_pure                                 0
% 4.01/0.98  fd_pseudo                               0
% 4.01/0.98  fd_cond                                 0
% 4.01/0.98  fd_pseudo_cond                          0
% 4.01/0.98  AC symbols                              0
% 4.01/0.98  
% 4.01/0.98  ------ Input Options Time Limit: Unbounded
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  Current options:
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ Proving...
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS status Theorem for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  fof(f6,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f28,plain,(
% 4.01/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f6])).
% 4.01/0.98  
% 4.01/0.98  fof(f2,axiom,(
% 4.01/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f24,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f2])).
% 4.01/0.98  
% 4.01/0.98  fof(f1,axiom,(
% 4.01/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f23,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.01/0.98    inference(cnf_transformation,[],[f1])).
% 4.01/0.98  
% 4.01/0.98  fof(f41,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f24,f23])).
% 4.01/0.98  
% 4.01/0.98  fof(f11,axiom,(
% 4.01/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f33,plain,(
% 4.01/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f11])).
% 4.01/0.98  
% 4.01/0.98  fof(f12,axiom,(
% 4.01/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f34,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f12])).
% 4.01/0.98  
% 4.01/0.98  fof(f13,axiom,(
% 4.01/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f35,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f13])).
% 4.01/0.98  
% 4.01/0.98  fof(f14,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f36,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f14])).
% 4.01/0.98  
% 4.01/0.98  fof(f15,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f37,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f15])).
% 4.01/0.98  
% 4.01/0.98  fof(f16,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f38,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f16])).
% 4.01/0.98  
% 4.01/0.98  fof(f42,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f37,f38])).
% 4.01/0.98  
% 4.01/0.98  fof(f43,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f36,f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f44,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f35,f43])).
% 4.01/0.98  
% 4.01/0.98  fof(f45,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f34,f44])).
% 4.01/0.98  
% 4.01/0.98  fof(f46,plain,(
% 4.01/0.98    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f33,f45])).
% 4.01/0.98  
% 4.01/0.98  fof(f48,plain,(
% 4.01/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f28,f41,f38,f46])).
% 4.01/0.98  
% 4.01/0.98  fof(f3,axiom,(
% 4.01/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f25,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f3])).
% 4.01/0.98  
% 4.01/0.98  fof(f49,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f25,f44,f44])).
% 4.01/0.98  
% 4.01/0.98  fof(f18,conjecture,(
% 4.01/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f19,negated_conjecture,(
% 4.01/0.98    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 4.01/0.98    inference(negated_conjecture,[],[f18])).
% 4.01/0.98  
% 4.01/0.98  fof(f20,plain,(
% 4.01/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 4.01/0.98    inference(ennf_transformation,[],[f19])).
% 4.01/0.98  
% 4.01/0.98  fof(f21,plain,(
% 4.01/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f22,plain,(
% 4.01/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 4.01/0.98  
% 4.01/0.98  fof(f40,plain,(
% 4.01/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f56,plain,(
% 4.01/0.98    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3)),
% 4.01/0.98    inference(definition_unfolding,[],[f40,f43,f43])).
% 4.01/0.98  
% 4.01/0.98  fof(f5,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f27,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f5])).
% 4.01/0.98  
% 4.01/0.98  fof(f51,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f27,f43,f43])).
% 4.01/0.98  
% 4.01/0.98  fof(f4,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 4.01/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f26,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f4])).
% 4.01/0.98  
% 4.01/0.98  fof(f50,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2)) )),
% 4.01/0.98    inference(definition_unfolding,[],[f26,f43,f43])).
% 4.01/0.98  
% 4.01/0.98  cnf(c_0,plain,
% 4.01/0.98      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 4.01/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_25,plain,
% 4.01/0.98      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k3_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1,plain,
% 4.01/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_24,plain,
% 4.01/0.98      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_312,plain,
% 4.01/0.98      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X2_36,X0_36,X3_36) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_24,c_25]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_13228,plain,
% 4.01/0.98      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_25,c_312]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8,negated_conjecture,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f56]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_17,negated_conjecture,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_13960,plain,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_13228,c_17]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_27,plain,
% 4.01/0.98      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 4.01/0.98      theory(equality) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_188,plain,
% 4.01/0.98      ( X0_35 != X1_35
% 4.01/0.98      | X0_35 = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != X1_35 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_886,plain,
% 4.01/0.98      ( X0_35 != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
% 4.01/0.98      | X0_35 = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_188]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2513,plain,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_886]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3,plain,
% 4.01/0.98      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X1,X2) ),
% 4.01/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_22,plain,
% 4.01/0.98      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1404,plain,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2,plain,
% 4.01/0.98      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X3,X2) ),
% 4.01/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_23,plain,
% 4.01/0.98      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X3_36,X2_36) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_162,plain,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_71,plain,
% 4.01/0.98      ( X0_35 != X1_35
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != X1_35
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = X0_35 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_133,plain,
% 4.01/0.98      ( X0_35 != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2)
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = X0_35
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_71]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_161,plain,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2)
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
% 4.01/0.98      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_133]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_66,plain,
% 4.01/0.98      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(contradiction,plain,
% 4.01/0.98      ( $false ),
% 4.01/0.98      inference(minisat,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_13960,c_2513,c_1404,c_162,c_161,c_66]) ).
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  ------                               Statistics
% 4.01/0.98  
% 4.01/0.98  ------ Selected
% 4.01/0.98  
% 4.01/0.98  total_time:                             0.434
% 4.01/0.98  
%------------------------------------------------------------------------------
