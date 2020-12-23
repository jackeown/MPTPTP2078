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

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 102 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   44 ( 103 expanded)
%              Number of equality atoms :   43 ( 102 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f36,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f37,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f22,f29,f37])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f20,f35,f35])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f32,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X1,X3) ),
    inference(definition_unfolding,[],[f21,f33,f33])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,plain,
    ( k2_xboole_0(k4_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35),k4_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35)) = k4_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,plain,
    ( k4_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k4_enumset1(X2_35,X2_35,X2_35,X2_35,X0_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_156,plain,
    ( k2_xboole_0(k4_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35),k4_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35,X3_35)) = k4_enumset1(X1_35,X1_35,X1_35,X2_35,X0_35,X3_35) ),
    inference(superposition,[status(thm)],[c_19,c_20])).

cnf(c_3644,plain,
    ( k4_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k4_enumset1(X2_35,X2_35,X2_35,X0_35,X1_35,X3_35) ),
    inference(superposition,[status(thm)],[c_20,c_156])).

cnf(c_6,negated_conjecture,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_4119,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_3644,c_14])).

cnf(c_2,plain,
    ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( k4_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k4_enumset1(X0_35,X0_35,X0_35,X2_35,X1_35,X3_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_221,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4119,c_221])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:27:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.58/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.98  
% 3.58/0.98  ------  iProver source info
% 3.58/0.98  
% 3.58/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.98  git: non_committed_changes: false
% 3.58/0.98  git: last_make_outside_of_git: false
% 3.58/0.98  
% 3.58/0.98  ------ 
% 3.58/0.98  ------ Parsing...
% 3.58/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/0.98  ------ Proving...
% 3.58/0.98  ------ Problem Properties 
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  clauses                                 7
% 3.58/0.98  conjectures                             1
% 3.58/0.98  EPR                                     0
% 3.58/0.98  Horn                                    7
% 3.58/0.98  unary                                   7
% 3.58/0.98  binary                                  0
% 3.58/0.98  lits                                    7
% 3.58/0.98  lits eq                                 7
% 3.58/0.98  fd_pure                                 0
% 3.58/0.98  fd_pseudo                               0
% 3.58/0.98  fd_cond                                 0
% 3.58/0.98  fd_pseudo_cond                          0
% 3.58/0.98  AC symbols                              0
% 3.58/0.98  
% 3.58/0.98  ------ Input Options Time Limit: Unbounded
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  ------ 
% 3.58/0.98  Current options:
% 3.58/0.98  ------ 
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  ------ Proving...
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  % SZS status Theorem for theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  fof(f4,axiom,(
% 3.58/0.98    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f22,plain,(
% 3.58/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f4])).
% 3.58/0.98  
% 3.58/0.98  fof(f7,axiom,(
% 3.58/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f25,plain,(
% 3.58/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f7])).
% 3.58/0.98  
% 3.58/0.98  fof(f8,axiom,(
% 3.58/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f26,plain,(
% 3.58/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f8])).
% 3.58/0.98  
% 3.58/0.98  fof(f9,axiom,(
% 3.58/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f27,plain,(
% 3.58/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f9])).
% 3.58/0.98  
% 3.58/0.98  fof(f10,axiom,(
% 3.58/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f28,plain,(
% 3.58/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f10])).
% 3.58/0.98  
% 3.58/0.98  fof(f11,axiom,(
% 3.58/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f29,plain,(
% 3.58/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f11])).
% 3.58/0.98  
% 3.58/0.98  fof(f33,plain,(
% 3.58/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.58/0.98    inference(definition_unfolding,[],[f28,f29])).
% 3.58/0.98  
% 3.58/0.98  fof(f35,plain,(
% 3.58/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.58/0.98    inference(definition_unfolding,[],[f27,f33])).
% 3.58/0.98  
% 3.58/0.98  fof(f36,plain,(
% 3.58/0.98    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.58/0.98    inference(definition_unfolding,[],[f26,f35])).
% 3.58/0.98  
% 3.58/0.98  fof(f37,plain,(
% 3.58/0.98    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.58/0.98    inference(definition_unfolding,[],[f25,f36])).
% 3.58/0.98  
% 3.58/0.98  fof(f39,plain,(
% 3.58/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.58/0.98    inference(definition_unfolding,[],[f22,f29,f37])).
% 3.58/0.98  
% 3.58/0.98  fof(f2,axiom,(
% 3.58/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f20,plain,(
% 3.58/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f2])).
% 3.58/0.98  
% 3.58/0.98  fof(f40,plain,(
% 3.58/0.98    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X2,X0)) )),
% 3.58/0.98    inference(definition_unfolding,[],[f20,f35,f35])).
% 3.58/0.98  
% 3.58/0.98  fof(f14,conjecture,(
% 3.58/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f15,negated_conjecture,(
% 3.58/0.98    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.58/0.98    inference(negated_conjecture,[],[f14])).
% 3.58/0.98  
% 3.58/0.98  fof(f16,plain,(
% 3.58/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 3.58/0.98    inference(ennf_transformation,[],[f15])).
% 3.58/0.98  
% 3.58/0.98  fof(f17,plain,(
% 3.58/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f18,plain,(
% 3.58/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.58/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 3.58/0.98  
% 3.58/0.98  fof(f32,plain,(
% 3.58/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.58/0.98    inference(cnf_transformation,[],[f18])).
% 3.58/0.98  
% 3.58/0.98  fof(f45,plain,(
% 3.58/0.98    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3)),
% 3.58/0.98    inference(definition_unfolding,[],[f32,f33,f33])).
% 3.58/0.98  
% 3.58/0.98  fof(f3,axiom,(
% 3.58/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f21,plain,(
% 3.58/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f3])).
% 3.58/0.98  
% 3.58/0.98  fof(f41,plain,(
% 3.58/0.98    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X1,X3)) )),
% 3.58/0.98    inference(definition_unfolding,[],[f21,f33,f33])).
% 3.58/0.98  
% 3.58/0.98  cnf(c_0,plain,
% 3.58/0.98      ( k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.58/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_20,plain,
% 3.58/0.98      ( k2_xboole_0(k4_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35),k4_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35)) = k4_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35) ),
% 3.58/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1,plain,
% 3.58/0.98      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X0,X1) ),
% 3.58/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_19,plain,
% 3.58/0.98      ( k4_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k4_enumset1(X2_35,X2_35,X2_35,X2_35,X0_35,X1_35) ),
% 3.58/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_156,plain,
% 3.58/0.98      ( k2_xboole_0(k4_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35,X2_35),k4_enumset1(X3_35,X3_35,X3_35,X3_35,X3_35,X3_35)) = k4_enumset1(X1_35,X1_35,X1_35,X2_35,X0_35,X3_35) ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_19,c_20]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3644,plain,
% 3.58/0.98      ( k4_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k4_enumset1(X2_35,X2_35,X2_35,X0_35,X1_35,X3_35) ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_20,c_156]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_6,negated_conjecture,
% 3.58/0.98      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3) ),
% 3.58/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_14,negated_conjecture,
% 3.58/0.98      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3) ),
% 3.58/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_4119,plain,
% 3.58/0.98      ( k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_3644,c_14]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_2,plain,
% 3.58/0.98      ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X1,X3) ),
% 3.58/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_18,plain,
% 3.58/0.98      ( k4_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35) = k4_enumset1(X0_35,X0_35,X0_35,X2_35,X1_35,X3_35) ),
% 3.58/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_221,plain,
% 3.58/0.98      ( k4_enumset1(sK0,sK0,sK0,sK2,sK1,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 3.58/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(contradiction,plain,
% 3.58/0.98      ( $false ),
% 3.58/0.98      inference(minisat,[status(thm)],[c_4119,c_221]) ).
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  ------                               Statistics
% 3.58/0.98  
% 3.58/0.98  ------ Selected
% 3.58/0.98  
% 3.58/0.98  total_time:                             0.179
% 3.58/0.98  
%------------------------------------------------------------------------------
