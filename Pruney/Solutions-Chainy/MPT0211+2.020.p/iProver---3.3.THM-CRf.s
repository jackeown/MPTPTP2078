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
% DateTime   : Thu Dec  3 11:28:26 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 228 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :   14 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :   59 ( 229 expanded)
%              Number of equality atoms :   58 ( 228 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f28,f48,f48])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X6,X7),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X6,X7),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f34,f45,f46,f48])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f32,f45,f46,f50])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f44,f45,f50,f50,f48])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f43,f48,f48])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k5_enumset1(X2_35,X2_35,X2_35,X2_35,X2_35,X0_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,plain,
    ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X5_35,X6_35,X4_35) ),
    inference(superposition,[status(thm)],[c_26,c_21])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,plain,
    ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35),k5_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3882,plain,
    ( k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X4_35) = k5_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35) ),
    inference(superposition,[status(thm)],[c_217,c_28])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_331,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_28,c_19])).

cnf(c_11653,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(superposition,[status(thm)],[c_26,c_331])).

cnf(c_13004,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(superposition,[status(thm)],[c_3882,c_11653])).

cnf(c_8,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,plain,
    ( k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X2_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_982,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13004,c_982])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.74/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.05  
% 2.74/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/1.05  
% 2.74/1.05  ------  iProver source info
% 2.74/1.05  
% 2.74/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.74/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/1.05  git: non_committed_changes: false
% 2.74/1.05  git: last_make_outside_of_git: false
% 2.74/1.05  
% 2.74/1.05  ------ 
% 2.74/1.05  ------ Parsing...
% 2.74/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/1.05  
% 2.74/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.74/1.05  
% 2.74/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/1.05  
% 2.74/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.74/1.05  ------ Proving...
% 2.74/1.05  ------ Problem Properties 
% 2.74/1.05  
% 2.74/1.05  
% 2.74/1.05  clauses                                 10
% 2.74/1.05  conjectures                             1
% 2.74/1.05  EPR                                     0
% 2.74/1.05  Horn                                    10
% 2.74/1.05  unary                                   10
% 2.74/1.05  binary                                  0
% 2.74/1.05  lits                                    10
% 2.74/1.05  lits eq                                 10
% 2.74/1.05  fd_pure                                 0
% 2.74/1.05  fd_pseudo                               0
% 2.74/1.05  fd_cond                                 0
% 2.74/1.05  fd_pseudo_cond                          0
% 2.74/1.05  AC symbols                              0
% 2.74/1.05  
% 2.74/1.05  ------ Input Options Time Limit: Unbounded
% 2.74/1.05  
% 2.74/1.05  
% 2.74/1.05  ------ 
% 2.74/1.05  Current options:
% 2.74/1.05  ------ 
% 2.74/1.05  
% 2.74/1.05  
% 2.74/1.05  
% 2.74/1.05  
% 2.74/1.05  ------ Proving...
% 2.74/1.05  
% 2.74/1.05  
% 2.74/1.05  % SZS status Theorem for theBenchmark.p
% 2.74/1.05  
% 2.74/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/1.05  
% 2.74/1.05  fof(f4,axiom,(
% 2.74/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f28,plain,(
% 2.74/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f4])).
% 2.74/1.05  
% 2.74/1.05  fof(f14,axiom,(
% 2.74/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f38,plain,(
% 2.74/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f14])).
% 2.74/1.05  
% 2.74/1.05  fof(f15,axiom,(
% 2.74/1.05    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f39,plain,(
% 2.74/1.05    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f15])).
% 2.74/1.05  
% 2.74/1.05  fof(f16,axiom,(
% 2.74/1.05    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f40,plain,(
% 2.74/1.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f16])).
% 2.74/1.05  
% 2.74/1.05  fof(f17,axiom,(
% 2.74/1.05    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f41,plain,(
% 2.74/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f17])).
% 2.74/1.05  
% 2.74/1.05  fof(f46,plain,(
% 2.74/1.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f40,f41])).
% 2.74/1.05  
% 2.74/1.05  fof(f47,plain,(
% 2.74/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f39,f46])).
% 2.74/1.05  
% 2.74/1.05  fof(f48,plain,(
% 2.74/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f38,f47])).
% 2.74/1.05  
% 2.74/1.05  fof(f54,plain,(
% 2.74/1.05    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f28,f48,f48])).
% 2.74/1.05  
% 2.74/1.05  fof(f18,axiom,(
% 2.74/1.05    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f42,plain,(
% 2.74/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f18])).
% 2.74/1.05  
% 2.74/1.05  fof(f10,axiom,(
% 2.74/1.05    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f34,plain,(
% 2.74/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f10])).
% 2.74/1.05  
% 2.74/1.05  fof(f3,axiom,(
% 2.74/1.05    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f27,plain,(
% 2.74/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f3])).
% 2.74/1.05  
% 2.74/1.05  fof(f2,axiom,(
% 2.74/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f26,plain,(
% 2.74/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.74/1.05    inference(cnf_transformation,[],[f2])).
% 2.74/1.05  
% 2.74/1.05  fof(f45,plain,(
% 2.74/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f27,f26])).
% 2.74/1.05  
% 2.74/1.05  fof(f52,plain,(
% 2.74/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X6,X7),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X6,X7),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f34,f45,f46,f48])).
% 2.74/1.05  
% 2.74/1.05  fof(f59,plain,(
% 2.74/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f42,f52])).
% 2.74/1.05  
% 2.74/1.05  fof(f8,axiom,(
% 2.74/1.05    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f32,plain,(
% 2.74/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f8])).
% 2.74/1.05  
% 2.74/1.05  fof(f13,axiom,(
% 2.74/1.05    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f37,plain,(
% 2.74/1.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f13])).
% 2.74/1.05  
% 2.74/1.05  fof(f50,plain,(
% 2.74/1.05    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f37,f48])).
% 2.74/1.05  
% 2.74/1.05  fof(f53,plain,(
% 2.74/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f32,f45,f46,f50])).
% 2.74/1.05  
% 2.74/1.05  fof(f20,conjecture,(
% 2.74/1.05    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f21,negated_conjecture,(
% 2.74/1.05    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.74/1.05    inference(negated_conjecture,[],[f20])).
% 2.74/1.05  
% 2.74/1.05  fof(f22,plain,(
% 2.74/1.05    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 2.74/1.05    inference(ennf_transformation,[],[f21])).
% 2.74/1.05  
% 2.74/1.05  fof(f23,plain,(
% 2.74/1.05    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.74/1.05    introduced(choice_axiom,[])).
% 2.74/1.05  
% 2.74/1.05  fof(f24,plain,(
% 2.74/1.05    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.74/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 2.74/1.05  
% 2.74/1.05  fof(f44,plain,(
% 2.74/1.05    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 2.74/1.05    inference(cnf_transformation,[],[f24])).
% 2.74/1.05  
% 2.74/1.05  fof(f61,plain,(
% 2.74/1.05    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 2.74/1.05    inference(definition_unfolding,[],[f44,f45,f50,f50,f48])).
% 2.74/1.05  
% 2.74/1.05  fof(f19,axiom,(
% 2.74/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 2.74/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.05  
% 2.74/1.05  fof(f43,plain,(
% 2.74/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 2.74/1.05    inference(cnf_transformation,[],[f19])).
% 2.74/1.05  
% 2.74/1.05  fof(f60,plain,(
% 2.74/1.05    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1)) )),
% 2.74/1.05    inference(definition_unfolding,[],[f43,f48,f48])).
% 2.74/1.05  
% 2.74/1.05  cnf(c_2,plain,
% 2.74/1.05      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 2.74/1.05      inference(cnf_transformation,[],[f54]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_26,plain,
% 2.74/1.05      ( k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k5_enumset1(X2_35,X2_35,X2_35,X2_35,X2_35,X0_35,X1_35) ),
% 2.74/1.05      inference(subtyping,[status(esa)],[c_2]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_7,plain,
% 2.74/1.05      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 2.74/1.05      inference(cnf_transformation,[],[f59]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_21,plain,
% 2.74/1.05      ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35) ),
% 2.74/1.05      inference(subtyping,[status(esa)],[c_7]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_217,plain,
% 2.74/1.05      ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35,X3_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X5_35,X6_35,X4_35) ),
% 2.74/1.05      inference(superposition,[status(thm)],[c_26,c_21]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_0,plain,
% 2.74/1.05      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 2.74/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_28,plain,
% 2.74/1.05      ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35),k5_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35) ),
% 2.74/1.05      inference(subtyping,[status(esa)],[c_0]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_3882,plain,
% 2.74/1.05      ( k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X4_35) = k5_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35) ),
% 2.74/1.05      inference(superposition,[status(thm)],[c_217,c_28]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_9,negated_conjecture,
% 2.74/1.05      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.74/1.05      inference(cnf_transformation,[],[f61]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_19,negated_conjecture,
% 2.74/1.05      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.74/1.05      inference(subtyping,[status(esa)],[c_9]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_331,plain,
% 2.74/1.05      ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.74/1.05      inference(superposition,[status(thm)],[c_28,c_19]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_11653,plain,
% 2.74/1.05      ( k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK0) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
% 2.74/1.05      inference(superposition,[status(thm)],[c_26,c_331]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_13004,plain,
% 2.74/1.05      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
% 2.74/1.05      inference(superposition,[status(thm)],[c_3882,c_11653]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_8,plain,
% 2.74/1.05      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1) ),
% 2.74/1.05      inference(cnf_transformation,[],[f60]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_20,plain,
% 2.74/1.05      ( k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X2_35,X1_35) ),
% 2.74/1.05      inference(subtyping,[status(esa)],[c_8]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(c_982,plain,
% 2.74/1.05      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
% 2.74/1.05      inference(instantiation,[status(thm)],[c_20]) ).
% 2.74/1.05  
% 2.74/1.05  cnf(contradiction,plain,
% 2.74/1.05      ( $false ),
% 2.74/1.05      inference(minisat,[status(thm)],[c_13004,c_982]) ).
% 2.74/1.05  
% 2.74/1.05  
% 2.74/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/1.05  
% 2.74/1.05  ------                               Statistics
% 2.74/1.05  
% 2.74/1.05  ------ Selected
% 2.74/1.05  
% 2.74/1.05  total_time:                             0.495
% 2.74/1.05  
%------------------------------------------------------------------------------
