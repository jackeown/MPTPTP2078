%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:55 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   40 (  78 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :   41 (  79 expanded)
%              Number of equality atoms :   40 (  78 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f31,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f32,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f20,f24,f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f18,f30,f30])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).

fof(f28,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f28,f24,f24])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
    inference(definition_unfolding,[],[f19,f24,f24])).

cnf(c_0,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,plain,
    ( k2_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35),k3_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35)) = k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,plain,
    ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X2_35,X2_35,X2_35,X0_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_144,plain,
    ( k2_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k3_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35)) = k3_enumset1(X1_35,X1_35,X2_35,X0_35,X3_35) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_2648,plain,
    ( k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35) = k3_enumset1(X2_35,X2_35,X0_35,X1_35,X3_35) ),
    inference(superposition,[status(thm)],[c_15,c_144])).

cnf(c_4,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3040,plain,
    ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2648,c_11])).

cnf(c_2,plain,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35) = k3_enumset1(X0_35,X0_35,X2_35,X1_35,X3_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_66,plain,
    ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3040,c_66])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.50/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/1.00  
% 3.50/1.00  ------  iProver source info
% 3.50/1.00  
% 3.50/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.50/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/1.00  git: non_committed_changes: false
% 3.50/1.00  git: last_make_outside_of_git: false
% 3.50/1.00  
% 3.50/1.00  ------ 
% 3.50/1.00  ------ Parsing...
% 3.50/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  ------ Proving...
% 3.50/1.00  ------ Problem Properties 
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  clauses                                 5
% 3.50/1.00  conjectures                             1
% 3.50/1.00  EPR                                     0
% 3.50/1.00  Horn                                    5
% 3.50/1.00  unary                                   5
% 3.50/1.00  binary                                  0
% 3.50/1.00  lits                                    5
% 3.50/1.00  lits eq                                 5
% 3.50/1.00  fd_pure                                 0
% 3.50/1.00  fd_pseudo                               0
% 3.50/1.00  fd_cond                                 0
% 3.50/1.00  fd_pseudo_cond                          0
% 3.50/1.00  AC symbols                              0
% 3.50/1.00  
% 3.50/1.00  ------ Input Options Time Limit: Unbounded
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ 
% 3.50/1.00  Current options:
% 3.50/1.00  ------ 
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Proving...
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS status Theorem for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  fof(f4,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f20,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f4])).
% 3.50/1.00  
% 3.50/1.00  fof(f5,axiom,(
% 3.50/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f21,plain,(
% 3.50/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f5])).
% 3.50/1.00  
% 3.50/1.00  fof(f6,axiom,(
% 3.50/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f22,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f6])).
% 3.50/1.00  
% 3.50/1.00  fof(f7,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f23,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f7])).
% 3.50/1.00  
% 3.50/1.00  fof(f8,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f24,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f8])).
% 3.50/1.00  
% 3.50/1.00  fof(f30,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f23,f24])).
% 3.50/1.00  
% 3.50/1.00  fof(f31,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f22,f30])).
% 3.50/1.00  
% 3.50/1.00  fof(f32,plain,(
% 3.50/1.00    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f21,f31])).
% 3.50/1.00  
% 3.50/1.00  fof(f35,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f20,f24,f32])).
% 3.50/1.00  
% 3.50/1.00  fof(f2,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f18,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f2])).
% 3.50/1.00  
% 3.50/1.00  fof(f36,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f18,f30,f30])).
% 3.50/1.00  
% 3.50/1.00  fof(f12,conjecture,(
% 3.50/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f13,negated_conjecture,(
% 3.50/1.00    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.50/1.00    inference(negated_conjecture,[],[f12])).
% 3.50/1.00  
% 3.50/1.00  fof(f14,plain,(
% 3.50/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 3.50/1.00    inference(ennf_transformation,[],[f13])).
% 3.50/1.00  
% 3.50/1.00  fof(f15,plain,(
% 3.50/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f16,plain,(
% 3.50/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).
% 3.50/1.00  
% 3.50/1.00  fof(f28,plain,(
% 3.50/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.50/1.00    inference(cnf_transformation,[],[f16])).
% 3.50/1.00  
% 3.50/1.00  fof(f39,plain,(
% 3.50/1.00    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3)),
% 3.50/1.00    inference(definition_unfolding,[],[f28,f24,f24])).
% 3.50/1.00  
% 3.50/1.00  fof(f3,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f19,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f3])).
% 3.50/1.00  
% 3.50/1.00  fof(f37,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f19,f24,f24])).
% 3.50/1.00  
% 3.50/1.00  cnf(c_0,plain,
% 3.50/1.00      ( k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 3.50/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_15,plain,
% 3.50/1.00      ( k2_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35),k3_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35)) = k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) ),
% 3.50/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1,plain,
% 3.50/1.00      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X0,X1) ),
% 3.50/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_14,plain,
% 3.50/1.00      ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X2_35,X2_35,X2_35,X0_35,X1_35) ),
% 3.50/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_144,plain,
% 3.50/1.00      ( k2_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35),k3_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35)) = k3_enumset1(X1_35,X1_35,X2_35,X0_35,X3_35) ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2648,plain,
% 3.50/1.00      ( k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35) = k3_enumset1(X2_35,X2_35,X0_35,X1_35,X3_35) ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_15,c_144]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_4,negated_conjecture,
% 3.50/1.00      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 3.50/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_11,negated_conjecture,
% 3.50/1.00      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK1,sK1,sK0,sK2,sK3) ),
% 3.50/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3040,plain,
% 3.50/1.00      ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_2648,c_11]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2,plain,
% 3.50/1.00      ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
% 3.50/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_13,plain,
% 3.50/1.00      ( k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35) = k3_enumset1(X0_35,X0_35,X2_35,X1_35,X3_35) ),
% 3.50/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_66,plain,
% 3.50/1.00      ( k3_enumset1(sK0,sK0,sK2,sK1,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(contradiction,plain,
% 3.50/1.00      ( $false ),
% 3.50/1.00      inference(minisat,[status(thm)],[c_3040,c_66]) ).
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  ------                               Statistics
% 3.50/1.00  
% 3.50/1.00  ------ Selected
% 3.50/1.00  
% 3.50/1.00  total_time:                             0.129
% 3.50/1.00  
%------------------------------------------------------------------------------
