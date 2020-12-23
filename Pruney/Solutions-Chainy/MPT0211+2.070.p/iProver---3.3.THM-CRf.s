%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:34 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 142 expanded)
%              Number of clauses        :   26 (  38 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 159 expanded)
%              Number of equality atoms :   70 ( 158 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f27,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f19,f15,f22,f27])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f16,f15,f22,f25])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f24,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f24,f15,f25,f25,f22])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_180,plain,
    ( k2_enumset1(X0_36,X1_36,X2_36,X2_36) = k2_enumset1(X0_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_16,c_13])).

cnf(c_414,plain,
    ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_180,c_13])).

cnf(c_2,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_14,plain,
    ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X3_36,X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_38,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK0,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_14,c_12])).

cnf(c_408,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_180,c_38])).

cnf(c_12590,plain,
    ( k2_enumset1(sK1,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_414,c_408])).

cnf(c_19,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_137,plain,
    ( X0_34 != X1_34
    | X0_34 = k2_enumset1(sK0,sK0,sK1,sK2)
    | k2_enumset1(sK0,sK0,sK1,sK2) != X1_34 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_472,plain,
    ( X0_34 != k2_enumset1(sK2,sK1,sK0,sK0)
    | X0_34 = k2_enumset1(sK0,sK0,sK1,sK2)
    | k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK1,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_2315,plain,
    ( k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK1,sK0,sK0)
    | k2_enumset1(sK1,sK0,sK0,sK2) != k2_enumset1(sK2,sK1,sK0,sK0)
    | k2_enumset1(sK1,sK0,sK0,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_837,plain,
    ( k2_enumset1(sK1,sK0,sK0,sK2) = k2_enumset1(sK2,sK1,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_15,plain,
    ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X0_36,X3_36,X2_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_144,plain,
    ( k2_enumset1(sK2,sK1,sK0,sK0) = k2_enumset1(sK2,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_53,plain,
    ( X0_34 != X1_34
    | k2_enumset1(sK0,sK0,sK1,sK2) != X1_34
    | k2_enumset1(sK0,sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_68,plain,
    ( X0_34 != k2_enumset1(sK2,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK1,sK2) = X0_34
    | k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_143,plain,
    ( k2_enumset1(sK2,sK1,sK0,sK0) != k2_enumset1(sK2,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK1,sK2) = k2_enumset1(sK2,sK1,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_49,plain,
    ( k2_enumset1(sK0,sK0,sK1,sK2) = k2_enumset1(sK2,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12590,c_2315,c_837,c_144,c_143,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:12:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.77/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/1.00  
% 3.77/1.00  ------  iProver source info
% 3.77/1.00  
% 3.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/1.00  git: non_committed_changes: false
% 3.77/1.00  git: last_make_outside_of_git: false
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  ------ Parsing...
% 3.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.77/1.00  ------ Proving...
% 3.77/1.00  ------ Problem Properties 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  clauses                                 5
% 3.77/1.00  conjectures                             1
% 3.77/1.00  EPR                                     0
% 3.77/1.00  Horn                                    5
% 3.77/1.00  unary                                   5
% 3.77/1.00  binary                                  0
% 3.77/1.00  lits                                    5
% 3.77/1.00  lits eq                                 5
% 3.77/1.00  fd_pure                                 0
% 3.77/1.00  fd_pseudo                               0
% 3.77/1.00  fd_cond                                 0
% 3.77/1.00  fd_pseudo_cond                          0
% 3.77/1.00  AC symbols                              0
% 3.77/1.00  
% 3.77/1.00  ------ Input Options Time Limit: Unbounded
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  Current options:
% 3.77/1.00  ------ 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ Proving...
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS status Theorem for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  fof(f5,axiom,(
% 3.77/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f19,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f5])).
% 3.77/1.00  
% 3.77/1.00  fof(f1,axiom,(
% 3.77/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f15,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f1])).
% 3.77/1.00  
% 3.77/1.00  fof(f6,axiom,(
% 3.77/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f20,plain,(
% 3.77/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f6])).
% 3.77/1.00  
% 3.77/1.00  fof(f7,axiom,(
% 3.77/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f21,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f7])).
% 3.77/1.00  
% 3.77/1.00  fof(f8,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f22,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f8])).
% 3.77/1.00  
% 3.77/1.00  fof(f25,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f21,f22])).
% 3.77/1.00  
% 3.77/1.00  fof(f27,plain,(
% 3.77/1.00    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f20,f25])).
% 3.77/1.00  
% 3.77/1.00  fof(f28,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f19,f15,f22,f27])).
% 3.77/1.00  
% 3.77/1.00  fof(f9,axiom,(
% 3.77/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f23,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f9])).
% 3.77/1.00  
% 3.77/1.00  fof(f2,axiom,(
% 3.77/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f16,plain,(
% 3.77/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f2])).
% 3.77/1.00  
% 3.77/1.00  fof(f26,plain,(
% 3.77/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f16,f15,f22,f25])).
% 3.77/1.00  
% 3.77/1.00  fof(f29,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f23,f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f4,axiom,(
% 3.77/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f18,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f4])).
% 3.77/1.00  
% 3.77/1.00  fof(f10,conjecture,(
% 3.77/1.00    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f11,negated_conjecture,(
% 3.77/1.00    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.77/1.00    inference(negated_conjecture,[],[f10])).
% 3.77/1.00  
% 3.77/1.00  fof(f12,plain,(
% 3.77/1.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 3.77/1.00    inference(ennf_transformation,[],[f11])).
% 3.77/1.00  
% 3.77/1.00  fof(f13,plain,(
% 3.77/1.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f14,plain,(
% 3.77/1.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 3.77/1.00  
% 3.77/1.00  fof(f24,plain,(
% 3.77/1.00    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 3.77/1.00    inference(cnf_transformation,[],[f14])).
% 3.77/1.00  
% 3.77/1.00  fof(f30,plain,(
% 3.77/1.00    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 3.77/1.00    inference(definition_unfolding,[],[f24,f15,f25,f25,f22])).
% 3.77/1.00  
% 3.77/1.00  fof(f3,axiom,(
% 3.77/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f17,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f3])).
% 3.77/1.00  
% 3.77/1.00  cnf(c_0,plain,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.77/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_16,plain,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X1_36,X2_36),k4_xboole_0(k2_enumset1(X3_36,X3_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X1_36,X2_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
% 3.77/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3,plain,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.77/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13,plain,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X2_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
% 3.77/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_180,plain,
% 3.77/1.00      ( k2_enumset1(X0_36,X1_36,X2_36,X2_36) = k2_enumset1(X0_36,X0_36,X1_36,X2_36) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_16,c_13]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_414,plain,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(X0_36,X0_36,X0_36,X1_36),k4_xboole_0(k2_enumset1(X2_36,X2_36,X3_36,X3_36),k2_enumset1(X0_36,X0_36,X0_36,X1_36))) = k2_enumset1(X0_36,X1_36,X2_36,X3_36) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_180,c_13]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2,plain,
% 3.77/1.00      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X0,X1,X2) ),
% 3.77/1.00      inference(cnf_transformation,[],[f18]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_14,plain,
% 3.77/1.00      ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X3_36,X0_36,X1_36,X2_36) ),
% 3.77/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4,negated_conjecture,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.77/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_12,negated_conjecture,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.77/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_38,plain,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK0,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_14,c_12]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_408,plain,
% 3.77/1.00      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_180,c_38]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_12590,plain,
% 3.77/1.00      ( k2_enumset1(sK1,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_414,c_408]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_19,plain,
% 3.77/1.00      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 3.77/1.00      theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_137,plain,
% 3.77/1.00      ( X0_34 != X1_34
% 3.77/1.00      | X0_34 = k2_enumset1(sK0,sK0,sK1,sK2)
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) != X1_34 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_472,plain,
% 3.77/1.00      ( X0_34 != k2_enumset1(sK2,sK1,sK0,sK0)
% 3.77/1.00      | X0_34 = k2_enumset1(sK0,sK0,sK1,sK2)
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK1,sK0,sK0) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_137]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2315,plain,
% 3.77/1.00      ( k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK1,sK0,sK0)
% 3.77/1.00      | k2_enumset1(sK1,sK0,sK0,sK2) != k2_enumset1(sK2,sK1,sK0,sK0)
% 3.77/1.00      | k2_enumset1(sK1,sK0,sK0,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_472]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_837,plain,
% 3.77/1.00      ( k2_enumset1(sK1,sK0,sK0,sK2) = k2_enumset1(sK2,sK1,sK0,sK0) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1,plain,
% 3.77/1.00      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15,plain,
% 3.77/1.00      ( k2_enumset1(X0_36,X1_36,X2_36,X3_36) = k2_enumset1(X0_36,X3_36,X2_36,X1_36) ),
% 3.77/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_144,plain,
% 3.77/1.00      ( k2_enumset1(sK2,sK1,sK0,sK0) = k2_enumset1(sK2,sK0,sK0,sK1) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_53,plain,
% 3.77/1.00      ( X0_34 != X1_34
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) != X1_34
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) = X0_34 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_68,plain,
% 3.77/1.00      ( X0_34 != k2_enumset1(sK2,sK0,sK0,sK1)
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) = X0_34
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK0,sK0,sK1) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_53]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_143,plain,
% 3.77/1.00      ( k2_enumset1(sK2,sK1,sK0,sK0) != k2_enumset1(sK2,sK0,sK0,sK1)
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK2,sK0,sK0,sK1)
% 3.77/1.00      | k2_enumset1(sK0,sK0,sK1,sK2) = k2_enumset1(sK2,sK1,sK0,sK0) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_68]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_49,plain,
% 3.77/1.00      ( k2_enumset1(sK0,sK0,sK1,sK2) = k2_enumset1(sK2,sK0,sK0,sK1) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(contradiction,plain,
% 3.77/1.00      ( $false ),
% 3.77/1.00      inference(minisat,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_12590,c_2315,c_837,c_144,c_143,c_49]) ).
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  ------                               Statistics
% 3.77/1.00  
% 3.77/1.00  ------ Selected
% 3.77/1.00  
% 3.77/1.00  total_time:                             0.439
% 3.77/1.00  
%------------------------------------------------------------------------------
