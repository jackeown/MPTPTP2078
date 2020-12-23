%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:55 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 136 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   52 ( 137 expanded)
%              Number of equality atoms :   51 ( 136 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f41,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f42,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f25,f37,f34,f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f23,f40,f40])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f36,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f36,f39,f39])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X1,X3) ),
    inference(definition_unfolding,[],[f24,f39,f39])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k3_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_167,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X2_36,X0_36,X3_36) ),
    inference(superposition,[status(thm)],[c_20,c_21])).

cnf(c_1428,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
    inference(superposition,[status(thm)],[c_21,c_167])).

cnf(c_6,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1607,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1428,c_15])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36,X3_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_222,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1607,c_222])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.29/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.99  
% 3.29/0.99  ------  iProver source info
% 3.29/0.99  
% 3.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.99  git: non_committed_changes: false
% 3.29/0.99  git: last_make_outside_of_git: false
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  ------ Parsing...
% 3.29/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.29/0.99  ------ Proving...
% 3.29/0.99  ------ Problem Properties 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  clauses                                 7
% 3.29/0.99  conjectures                             1
% 3.29/0.99  EPR                                     0
% 3.29/0.99  Horn                                    7
% 3.29/0.99  unary                                   7
% 3.29/0.99  binary                                  0
% 3.29/0.99  lits                                    7
% 3.29/0.99  lits eq                                 7
% 3.29/0.99  fd_pure                                 0
% 3.29/0.99  fd_pseudo                               0
% 3.29/0.99  fd_cond                                 0
% 3.29/0.99  fd_pseudo_cond                          0
% 3.29/0.99  AC symbols                              0
% 3.29/0.99  
% 3.29/0.99  ------ Input Options Time Limit: Unbounded
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  Current options:
% 3.29/0.99  ------ 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ Proving...
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS status Theorem for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  fof(f5,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f25,plain,(
% 3.29/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f5])).
% 3.29/0.99  
% 3.29/0.99  fof(f2,axiom,(
% 3.29/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f22,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f2])).
% 3.29/0.99  
% 3.29/0.99  fof(f1,axiom,(
% 3.29/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f21,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f1])).
% 3.29/0.99  
% 3.29/0.99  fof(f37,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f22,f21])).
% 3.29/0.99  
% 3.29/0.99  fof(f9,axiom,(
% 3.29/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f29,plain,(
% 3.29/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f9])).
% 3.29/0.99  
% 3.29/0.99  fof(f10,axiom,(
% 3.29/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f30,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f10])).
% 3.29/0.99  
% 3.29/0.99  fof(f11,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f31,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f11])).
% 3.29/0.99  
% 3.29/0.99  fof(f12,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f32,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f12])).
% 3.29/0.99  
% 3.29/0.99  fof(f13,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f33,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f13])).
% 3.29/0.99  
% 3.29/0.99  fof(f14,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f34,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f14])).
% 3.29/0.99  
% 3.29/0.99  fof(f38,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f33,f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f39,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f32,f38])).
% 3.29/0.99  
% 3.29/0.99  fof(f40,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f31,f39])).
% 3.29/0.99  
% 3.29/0.99  fof(f41,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f30,f40])).
% 3.29/0.99  
% 3.29/0.99  fof(f42,plain,(
% 3.29/0.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f29,f41])).
% 3.29/0.99  
% 3.29/0.99  fof(f44,plain,(
% 3.29/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f25,f37,f34,f42])).
% 3.29/0.99  
% 3.29/0.99  fof(f3,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f23,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f3])).
% 3.29/0.99  
% 3.29/0.99  fof(f45,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f23,f40,f40])).
% 3.29/0.99  
% 3.29/0.99  fof(f16,conjecture,(
% 3.29/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f17,negated_conjecture,(
% 3.29/0.99    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.29/0.99    inference(negated_conjecture,[],[f16])).
% 3.29/0.99  
% 3.29/0.99  fof(f18,plain,(
% 3.29/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 3.29/0.99    inference(ennf_transformation,[],[f17])).
% 3.29/0.99  
% 3.29/0.99  fof(f19,plain,(
% 3.29/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f20,plain,(
% 3.29/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 3.29/0.99  
% 3.29/0.99  fof(f36,plain,(
% 3.29/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.29/0.99    inference(cnf_transformation,[],[f20])).
% 3.29/0.99  
% 3.29/0.99  fof(f50,plain,(
% 3.29/0.99    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3)),
% 3.29/0.99    inference(definition_unfolding,[],[f36,f39,f39])).
% 3.29/0.99  
% 3.29/0.99  fof(f4,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f24,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f4])).
% 3.29/0.99  
% 3.29/0.99  fof(f46,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X1,X3)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f24,f39,f39])).
% 3.29/0.99  
% 3.29/0.99  cnf(c_0,plain,
% 3.29/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.29/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_21,plain,
% 3.29/0.99      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36),k5_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k3_xboole_0(k5_enumset1(X6_36,X6_36,X6_36,X6_36,X6_36,X6_36,X6_36),k5_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36,X5_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 3.29/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1,plain,
% 3.29/0.99      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_20,plain,
% 3.29/0.99      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
% 3.29/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_167,plain,
% 3.29/0.99      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36,X3_36,X3_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X2_36,X0_36,X3_36) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_20,c_21]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1428,plain,
% 3.29/0.99      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36,X3_36) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_21,c_167]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6,negated_conjecture,
% 3.29/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 3.29/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_15,negated_conjecture,
% 3.29/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 3.29/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1607,plain,
% 3.29/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1428,c_15]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2,plain,
% 3.29/0.99      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X1,X3) ),
% 3.29/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_19,plain,
% 3.29/0.99      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36) = k5_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36,X3_36) ),
% 3.29/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_222,plain,
% 3.29/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(contradiction,plain,
% 3.29/0.99      ( $false ),
% 3.29/0.99      inference(minisat,[status(thm)],[c_1607,c_222]) ).
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  ------                               Statistics
% 3.29/0.99  
% 3.29/0.99  ------ Selected
% 3.29/0.99  
% 3.29/0.99  total_time:                             0.153
% 3.29/0.99  
%------------------------------------------------------------------------------
