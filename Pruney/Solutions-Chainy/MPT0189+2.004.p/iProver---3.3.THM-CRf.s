%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:51 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 110 expanded)
%              Number of clauses        :   13 (  17 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   43 ( 111 expanded)
%              Number of equality atoms :   42 ( 110 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f43,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f37,f37])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f23,f35,f30,f38])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).

fof(f34,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f34,f30,f30])).

cnf(c_1,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_102,plain,
    ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(superposition,[status(thm)],[c_19,c_20])).

cnf(c_999,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36))))))) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_102,c_20])).

cnf(c_1002,plain,
    ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(demodulation,[status(thm)],[c_999,c_20])).

cnf(c_5,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1434,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1002,c_15])).

cnf(c_21,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_72,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1434,c_72])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.64/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/0.99  
% 2.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/0.99  
% 2.64/0.99  ------  iProver source info
% 2.64/0.99  
% 2.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/0.99  git: non_committed_changes: false
% 2.64/0.99  git: last_make_outside_of_git: false
% 2.64/0.99  
% 2.64/0.99  ------ 
% 2.64/0.99  ------ Parsing...
% 2.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.64/0.99  ------ Proving...
% 2.64/0.99  ------ Problem Properties 
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  clauses                                 6
% 2.64/0.99  conjectures                             1
% 2.64/0.99  EPR                                     0
% 2.64/0.99  Horn                                    6
% 2.64/0.99  unary                                   6
% 2.64/0.99  binary                                  0
% 2.64/0.99  lits                                    6
% 2.64/0.99  lits eq                                 6
% 2.64/0.99  fd_pure                                 0
% 2.64/0.99  fd_pseudo                               0
% 2.64/0.99  fd_cond                                 0
% 2.64/0.99  fd_pseudo_cond                          0
% 2.64/0.99  AC symbols                              0
% 2.64/0.99  
% 2.64/0.99  ------ Input Options Time Limit: Unbounded
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  ------ 
% 2.64/0.99  Current options:
% 2.64/0.99  ------ 
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  ------ Proving...
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  % SZS status Theorem for theBenchmark.p
% 2.64/0.99  
% 2.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/0.99  
% 2.64/0.99  fof(f3,axiom,(
% 2.64/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f22,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f3])).
% 2.64/0.99  
% 2.64/0.99  fof(f9,axiom,(
% 2.64/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f28,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f9])).
% 2.64/0.99  
% 2.64/0.99  fof(f10,axiom,(
% 2.64/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f29,plain,(
% 2.64/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f10])).
% 2.64/0.99  
% 2.64/0.99  fof(f11,axiom,(
% 2.64/0.99    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f30,plain,(
% 2.64/0.99    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f11])).
% 2.64/0.99  
% 2.64/0.99  fof(f36,plain,(
% 2.64/0.99    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f29,f30])).
% 2.64/0.99  
% 2.64/0.99  fof(f37,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f28,f36])).
% 2.64/0.99  
% 2.64/0.99  fof(f43,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f22,f37,f37])).
% 2.64/0.99  
% 2.64/0.99  fof(f4,axiom,(
% 2.64/0.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f23,plain,(
% 2.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f4])).
% 2.64/0.99  
% 2.64/0.99  fof(f2,axiom,(
% 2.64/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f21,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f2])).
% 2.64/0.99  
% 2.64/0.99  fof(f1,axiom,(
% 2.64/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f20,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.64/0.99    inference(cnf_transformation,[],[f1])).
% 2.64/0.99  
% 2.64/0.99  fof(f35,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f21,f20])).
% 2.64/0.99  
% 2.64/0.99  fof(f8,axiom,(
% 2.64/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f27,plain,(
% 2.64/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f8])).
% 2.64/0.99  
% 2.64/0.99  fof(f38,plain,(
% 2.64/0.99    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f27,f37])).
% 2.64/0.99  
% 2.64/0.99  fof(f42,plain,(
% 2.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f23,f35,f30,f38])).
% 2.64/0.99  
% 2.64/0.99  fof(f15,conjecture,(
% 2.64/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f16,negated_conjecture,(
% 2.64/0.99    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.64/0.99    inference(negated_conjecture,[],[f15])).
% 2.64/0.99  
% 2.64/0.99  fof(f17,plain,(
% 2.64/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 2.64/0.99    inference(ennf_transformation,[],[f16])).
% 2.64/0.99  
% 2.64/0.99  fof(f18,plain,(
% 2.64/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.64/0.99    introduced(choice_axiom,[])).
% 2.64/0.99  
% 2.64/0.99  fof(f19,plain,(
% 2.64/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).
% 2.64/0.99  
% 2.64/0.99  fof(f34,plain,(
% 2.64/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.64/0.99    inference(cnf_transformation,[],[f19])).
% 2.64/0.99  
% 2.64/0.99  fof(f47,plain,(
% 2.64/0.99    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3)),
% 2.64/0.99    inference(definition_unfolding,[],[f34,f30,f30])).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1,plain,
% 2.64/0.99      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_19,plain,
% 2.64/0.99      ( k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36) = k3_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36) ),
% 2.64/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_0,plain,
% 2.64/0.99      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 2.64/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_20,plain,
% 2.64/0.99      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36),k5_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_xboole_0(k3_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36),k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36)))) = k3_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 2.64/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_102,plain,
% 2.64/0.99      ( k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))) = k3_enumset1(X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_19,c_20]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_999,plain,
% 2.64/0.99      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36)))),k5_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k3_xboole_0(k3_enumset1(X3_36,X3_36,X3_36,X3_36,X3_36),k5_xboole_0(k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_xboole_0(k3_enumset1(X2_36,X2_36,X2_36,X2_36,X2_36),k3_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36))))))) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_102,c_20]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1002,plain,
% 2.64/0.99      ( k3_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36) = k3_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36) ),
% 2.64/0.99      inference(demodulation,[status(thm)],[c_999,c_20]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_5,negated_conjecture,
% 2.64/0.99      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 2.64/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_15,negated_conjecture,
% 2.64/0.99      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 2.64/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1434,plain,
% 2.64/0.99      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 2.64/0.99      inference(demodulation,[status(thm)],[c_1002,c_15]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_21,plain,( X0_35 = X0_35 ),theory(equality) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_72,plain,
% 2.64/0.99      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(contradiction,plain,
% 2.64/0.99      ( $false ),
% 2.64/0.99      inference(minisat,[status(thm)],[c_1434,c_72]) ).
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/0.99  
% 2.64/0.99  ------                               Statistics
% 2.64/0.99  
% 2.64/0.99  ------ Selected
% 2.64/0.99  
% 2.64/0.99  total_time:                             0.167
% 2.64/0.99  
%------------------------------------------------------------------------------
