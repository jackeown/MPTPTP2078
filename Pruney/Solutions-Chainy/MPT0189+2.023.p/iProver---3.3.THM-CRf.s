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
% DateTime   : Thu Dec  3 11:27:54 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   45 (  88 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 (  89 expanded)
%              Number of equality atoms :   45 (  88 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f42,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f43,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f27,f39,f35,f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f25,f41,f41])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).

fof(f38,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f38,f35,f35])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
    inference(definition_unfolding,[],[f26,f35,f35])).

cnf(c_0,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) = k3_enumset1(X2_36,X2_36,X2_36,X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_169,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X1_36,X1_36,X2_36,X0_36,X3_36) ),
    inference(superposition,[status(thm)],[c_23,c_24])).

cnf(c_3447,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X2_36,X2_36,X0_36,X1_36,X3_36) ),
    inference(superposition,[status(thm)],[c_24,c_169])).

cnf(c_7,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3928,plain,
    ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_3447,c_17])).

cnf(c_2,plain,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X2_36,X1_36,X3_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_344,plain,
    ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3928,c_344])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.79/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.98  
% 3.79/0.98  ------  iProver source info
% 3.79/0.98  
% 3.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.98  git: non_committed_changes: false
% 3.79/0.98  git: last_make_outside_of_git: false
% 3.79/0.98  
% 3.79/0.98  ------ 
% 3.79/0.98  ------ Parsing...
% 3.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.79/0.98  ------ Proving...
% 3.79/0.98  ------ Problem Properties 
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  clauses                                 8
% 3.79/0.98  conjectures                             1
% 3.79/0.98  EPR                                     0
% 3.79/0.98  Horn                                    8
% 3.79/0.98  unary                                   8
% 3.79/0.98  binary                                  0
% 3.79/0.98  lits                                    8
% 3.79/0.98  lits eq                                 8
% 3.79/0.98  fd_pure                                 0
% 3.79/0.98  fd_pseudo                               0
% 3.79/0.98  fd_cond                                 0
% 3.79/0.98  fd_pseudo_cond                          0
% 3.79/0.98  AC symbols                              0
% 3.79/0.98  
% 3.79/0.98  ------ Input Options Time Limit: Unbounded
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  ------ 
% 3.79/0.98  Current options:
% 3.79/0.98  ------ 
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  ------ Proving...
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  % SZS status Theorem for theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  fof(f6,axiom,(
% 3.79/0.98    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f27,plain,(
% 3.79/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f6])).
% 3.79/0.98  
% 3.79/0.98  fof(f2,axiom,(
% 3.79/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f23,plain,(
% 3.79/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f2])).
% 3.79/0.98  
% 3.79/0.98  fof(f1,axiom,(
% 3.79/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f22,plain,(
% 3.79/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.79/0.98    inference(cnf_transformation,[],[f1])).
% 3.79/0.98  
% 3.79/0.98  fof(f39,plain,(
% 3.79/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.79/0.98    inference(definition_unfolding,[],[f23,f22])).
% 3.79/0.98  
% 3.79/0.98  fof(f11,axiom,(
% 3.79/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f32,plain,(
% 3.79/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f11])).
% 3.79/0.98  
% 3.79/0.98  fof(f12,axiom,(
% 3.79/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f33,plain,(
% 3.79/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f12])).
% 3.79/0.98  
% 3.79/0.98  fof(f13,axiom,(
% 3.79/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f34,plain,(
% 3.79/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f13])).
% 3.79/0.98  
% 3.79/0.98  fof(f14,axiom,(
% 3.79/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f35,plain,(
% 3.79/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f14])).
% 3.79/0.98  
% 3.79/0.98  fof(f41,plain,(
% 3.79/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.79/0.98    inference(definition_unfolding,[],[f34,f35])).
% 3.79/0.98  
% 3.79/0.98  fof(f42,plain,(
% 3.79/0.98    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.79/0.98    inference(definition_unfolding,[],[f33,f41])).
% 3.79/0.98  
% 3.79/0.98  fof(f43,plain,(
% 3.79/0.98    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.79/0.98    inference(definition_unfolding,[],[f32,f42])).
% 3.79/0.98  
% 3.79/0.98  fof(f46,plain,(
% 3.79/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.79/0.98    inference(definition_unfolding,[],[f27,f39,f35,f43])).
% 3.79/0.98  
% 3.79/0.98  fof(f4,axiom,(
% 3.79/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f25,plain,(
% 3.79/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f4])).
% 3.79/0.98  
% 3.79/0.98  fof(f47,plain,(
% 3.79/0.98    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0)) )),
% 3.79/0.98    inference(definition_unfolding,[],[f25,f41,f41])).
% 3.79/0.98  
% 3.79/0.98  fof(f17,conjecture,(
% 3.79/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f18,negated_conjecture,(
% 3.79/0.98    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.79/0.98    inference(negated_conjecture,[],[f17])).
% 3.79/0.98  
% 3.79/0.98  fof(f19,plain,(
% 3.79/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 3.79/0.98    inference(ennf_transformation,[],[f18])).
% 3.79/0.98  
% 3.79/0.98  fof(f20,plain,(
% 3.79/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.79/0.98    introduced(choice_axiom,[])).
% 3.79/0.98  
% 3.79/0.98  fof(f21,plain,(
% 3.79/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).
% 3.79/0.98  
% 3.79/0.98  fof(f38,plain,(
% 3.79/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.79/0.98    inference(cnf_transformation,[],[f21])).
% 3.79/0.98  
% 3.79/0.98  fof(f53,plain,(
% 3.79/0.98    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3)),
% 3.79/0.98    inference(definition_unfolding,[],[f38,f35,f35])).
% 3.79/0.98  
% 3.79/0.98  fof(f5,axiom,(
% 3.79/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f26,plain,(
% 3.79/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f5])).
% 3.79/0.98  
% 3.79/0.98  fof(f48,plain,(
% 3.79/0.98    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)) )),
% 3.79/0.98    inference(definition_unfolding,[],[f26,f35,f35])).
% 3.79/0.98  
% 3.79/0.98  cnf(c_0,plain,
% 3.79/0.98      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 3.79/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_24,plain,
% 3.79/0.98      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1,plain,
% 3.79/0.98      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X0,X1) ),
% 3.79/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_23,plain,
% 3.79/0.98      ( k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36) = k3_enumset1(X2_36,X2_36,X2_36,X0_36,X1_36) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_169,plain,
% 3.79/0.98      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36)))) = k3_enumset1(X1_36,X1_36,X2_36,X0_36,X3_36) ),
% 3.79/0.98      inference(superposition,[status(thm)],[c_23,c_24]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_3447,plain,
% 3.79/0.98      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X2_36,X2_36,X0_36,X1_36,X3_36) ),
% 3.79/0.98      inference(superposition,[status(thm)],[c_24,c_169]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_7,negated_conjecture,
% 3.79/0.98      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 3.79/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_17,negated_conjecture,
% 3.79/0.98      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_3928,plain,
% 3.79/0.98      ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 3.79/0.98      inference(superposition,[status(thm)],[c_3447,c_17]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_2,plain,
% 3.79/0.98      ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
% 3.79/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_22,plain,
% 3.79/0.98      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X0_36,X0_36,X2_36,X1_36,X3_36) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_344,plain,
% 3.79/0.98      ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(contradiction,plain,
% 3.79/0.98      ( $false ),
% 3.79/0.98      inference(minisat,[status(thm)],[c_3928,c_344]) ).
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  ------                               Statistics
% 3.79/0.98  
% 3.79/0.98  ------ Selected
% 3.79/0.98  
% 3.79/0.98  total_time:                             0.182
% 3.79/0.98  
%------------------------------------------------------------------------------
