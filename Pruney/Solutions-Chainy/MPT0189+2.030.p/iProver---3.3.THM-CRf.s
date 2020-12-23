%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:55 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 162 expanded)
%              Number of clauses        :   20 (  22 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   70 ( 171 expanded)
%              Number of equality atoms :   69 ( 170 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    3 (   1 average)
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

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f26,f43,f43])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f27,f43,f43])).

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

cnf(c_18133,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
    inference(superposition,[status(thm)],[c_25,c_312])).

cnf(c_8,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_19051,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_18133,c_17])).

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

cnf(c_878,plain,
    ( X0_35 != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
    | X0_35 = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_1768,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_162,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X2_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_62,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19051,c_1768,c_162,c_62])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.57/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.48  
% 7.57/1.48  ------  iProver source info
% 7.57/1.48  
% 7.57/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.48  git: non_committed_changes: false
% 7.57/1.48  git: last_make_outside_of_git: false
% 7.57/1.48  
% 7.57/1.48  ------ 
% 7.57/1.48  ------ Parsing...
% 7.57/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.48  ------ Proving...
% 7.57/1.48  ------ Problem Properties 
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  clauses                                 9
% 7.57/1.48  conjectures                             1
% 7.57/1.48  EPR                                     0
% 7.57/1.48  Horn                                    9
% 7.57/1.48  unary                                   9
% 7.57/1.48  binary                                  0
% 7.57/1.48  lits                                    9
% 7.57/1.48  lits eq                                 9
% 7.57/1.48  fd_pure                                 0
% 7.57/1.48  fd_pseudo                               0
% 7.57/1.48  fd_cond                                 0
% 7.57/1.48  fd_pseudo_cond                          0
% 7.57/1.48  AC symbols                              0
% 7.57/1.48  
% 7.57/1.48  ------ Input Options Time Limit: Unbounded
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  ------ 
% 7.57/1.48  Current options:
% 7.57/1.48  ------ 
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  ------ Proving...
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  % SZS status Theorem for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  fof(f6,axiom,(
% 7.57/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f28,plain,(
% 7.57/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f6])).
% 7.57/1.48  
% 7.57/1.48  fof(f2,axiom,(
% 7.57/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f24,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f2])).
% 7.57/1.48  
% 7.57/1.48  fof(f1,axiom,(
% 7.57/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f23,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.57/1.48    inference(cnf_transformation,[],[f1])).
% 7.57/1.48  
% 7.57/1.48  fof(f41,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f24,f23])).
% 7.57/1.48  
% 7.57/1.48  fof(f11,axiom,(
% 7.57/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f33,plain,(
% 7.57/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f11])).
% 7.57/1.48  
% 7.57/1.48  fof(f12,axiom,(
% 7.57/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f34,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f12])).
% 7.57/1.48  
% 7.57/1.48  fof(f13,axiom,(
% 7.57/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f35,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f13])).
% 7.57/1.48  
% 7.57/1.48  fof(f14,axiom,(
% 7.57/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f36,plain,(
% 7.57/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f14])).
% 7.57/1.48  
% 7.57/1.48  fof(f15,axiom,(
% 7.57/1.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f37,plain,(
% 7.57/1.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f15])).
% 7.57/1.48  
% 7.57/1.48  fof(f16,axiom,(
% 7.57/1.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f38,plain,(
% 7.57/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f16])).
% 7.57/1.48  
% 7.57/1.48  fof(f42,plain,(
% 7.57/1.48    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f37,f38])).
% 7.57/1.48  
% 7.57/1.48  fof(f43,plain,(
% 7.57/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f36,f42])).
% 7.57/1.48  
% 7.57/1.48  fof(f44,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f35,f43])).
% 7.57/1.48  
% 7.57/1.48  fof(f45,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f34,f44])).
% 7.57/1.48  
% 7.57/1.48  fof(f46,plain,(
% 7.57/1.48    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f33,f45])).
% 7.57/1.48  
% 7.57/1.48  fof(f48,plain,(
% 7.57/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f28,f41,f38,f46])).
% 7.57/1.48  
% 7.57/1.48  fof(f3,axiom,(
% 7.57/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f25,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f3])).
% 7.57/1.48  
% 7.57/1.48  fof(f49,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f25,f44,f44])).
% 7.57/1.48  
% 7.57/1.48  fof(f18,conjecture,(
% 7.57/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f19,negated_conjecture,(
% 7.57/1.48    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 7.57/1.48    inference(negated_conjecture,[],[f18])).
% 7.57/1.48  
% 7.57/1.48  fof(f20,plain,(
% 7.57/1.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 7.57/1.48    inference(ennf_transformation,[],[f19])).
% 7.57/1.48  
% 7.57/1.48  fof(f21,plain,(
% 7.57/1.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 7.57/1.48    introduced(choice_axiom,[])).
% 7.57/1.48  
% 7.57/1.48  fof(f22,plain,(
% 7.57/1.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 7.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 7.57/1.48  
% 7.57/1.48  fof(f40,plain,(
% 7.57/1.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 7.57/1.48    inference(cnf_transformation,[],[f22])).
% 7.57/1.48  
% 7.57/1.48  fof(f56,plain,(
% 7.57/1.48    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3)),
% 7.57/1.48    inference(definition_unfolding,[],[f40,f43,f43])).
% 7.57/1.48  
% 7.57/1.48  fof(f4,axiom,(
% 7.57/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f26,plain,(
% 7.57/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f4])).
% 7.57/1.48  
% 7.57/1.48  fof(f50,plain,(
% 7.57/1.48    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f26,f43,f43])).
% 7.57/1.48  
% 7.57/1.48  fof(f5,axiom,(
% 7.57/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f27,plain,(
% 7.57/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f5])).
% 7.57/1.48  
% 7.57/1.48  fof(f51,plain,(
% 7.57/1.48    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1)) )),
% 7.57/1.48    inference(definition_unfolding,[],[f27,f43,f43])).
% 7.57/1.48  
% 7.57/1.48  cnf(c_0,plain,
% 7.57/1.48      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 7.57/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_25,plain,
% 7.57/1.48      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k3_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1,plain,
% 7.57/1.48      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 7.57/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_24,plain,
% 7.57/1.48      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_312,plain,
% 7.57/1.48      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X2_36,X0_36,X3_36) ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_24,c_25]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_18133,plain,
% 7.57/1.48      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_25,c_312]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_8,negated_conjecture,
% 7.57/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 7.57/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_17,negated_conjecture,
% 7.57/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_19051,plain,
% 7.57/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 7.57/1.48      inference(superposition,[status(thm)],[c_18133,c_17]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_27,plain,
% 7.57/1.48      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 7.57/1.48      theory(equality) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_188,plain,
% 7.57/1.48      ( X0_35 != X1_35
% 7.57/1.48      | X0_35 = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
% 7.57/1.48      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != X1_35 ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_878,plain,
% 7.57/1.48      ( X0_35 != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
% 7.57/1.48      | X0_35 = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
% 7.57/1.48      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_188]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_1768,plain,
% 7.57/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1)
% 7.57/1.48      | k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3)
% 7.57/1.48      | k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_878]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_2,plain,
% 7.57/1.48      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X1,X2) ),
% 7.57/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_23,plain,
% 7.57/1.48      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X1_36,X2_36) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_162,plain,
% 7.57/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_3,plain,
% 7.57/1.48      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
% 7.57/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_22,plain,
% 7.57/1.48      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X3_36,X2_36,X1_36) ),
% 7.57/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(c_62,plain,
% 7.57/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
% 7.57/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.57/1.48  
% 7.57/1.48  cnf(contradiction,plain,
% 7.57/1.48      ( $false ),
% 7.57/1.48      inference(minisat,[status(thm)],[c_19051,c_1768,c_162,c_62]) ).
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  ------                               Statistics
% 7.57/1.48  
% 7.57/1.48  ------ Selected
% 7.57/1.48  
% 7.57/1.48  total_time:                             0.836
% 7.57/1.48  
%------------------------------------------------------------------------------
