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
% DateTime   : Thu Dec  3 11:24:56 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 144 expanded)
%              Number of clauses        :   21 (  51 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 ( 145 expanded)
%              Number of equality atoms :   47 ( 144 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f38,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f24,f33])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f26,f33])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_641,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_681,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_641])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_51,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_9,c_0])).

cnf(c_4247,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_681,c_51])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_763,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_3])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_650,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_682,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_650,c_641])).

cnf(c_1032,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_682])).

cnf(c_1293,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_763,c_1032])).

cnf(c_1331,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1293,c_650])).

cnf(c_1286,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_5,c_1032])).

cnf(c_1342,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1286,c_1032])).

cnf(c_4248,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4247,c_1331,c_1342])).

cnf(c_5023,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4248,c_0])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.63/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/1.00  
% 3.63/1.00  ------  iProver source info
% 3.63/1.00  
% 3.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/1.00  git: non_committed_changes: false
% 3.63/1.00  git: last_make_outside_of_git: false
% 3.63/1.00  
% 3.63/1.00  ------ 
% 3.63/1.00  ------ Parsing...
% 3.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  ------ Proving...
% 3.63/1.00  ------ Problem Properties 
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  clauses                                 14
% 3.63/1.00  conjectures                             1
% 3.63/1.00  EPR                                     0
% 3.63/1.00  Horn                                    14
% 3.63/1.00  unary                                   13
% 3.63/1.00  binary                                  0
% 3.63/1.00  lits                                    17
% 3.63/1.00  lits eq                                 14
% 3.63/1.00  fd_pure                                 0
% 3.63/1.00  fd_pseudo                               0
% 3.63/1.00  fd_cond                                 0
% 3.63/1.00  fd_pseudo_cond                          1
% 3.63/1.00  AC symbols                              1
% 3.63/1.00  
% 3.63/1.00  ------ Input Options Time Limit: Unbounded
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing...
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.63/1.00  Current options:
% 3.63/1.00  ------ 
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  % SZS status Theorem for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00   Resolution empty clause
% 3.63/1.00  
% 3.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  fof(f7,axiom,(
% 3.63/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f29,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.63/1.00    inference(cnf_transformation,[],[f7])).
% 3.63/1.00  
% 3.63/1.00  fof(f12,axiom,(
% 3.63/1.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f34,plain,(
% 3.63/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f12])).
% 3.63/1.00  
% 3.63/1.00  fof(f1,axiom,(
% 3.63/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f23,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f1])).
% 3.63/1.00  
% 3.63/1.00  fof(f16,conjecture,(
% 3.63/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f17,negated_conjecture,(
% 3.63/1.00    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.63/1.00    inference(negated_conjecture,[],[f16])).
% 3.63/1.00  
% 3.63/1.00  fof(f20,plain,(
% 3.63/1.00    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.63/1.00    inference(ennf_transformation,[],[f17])).
% 3.63/1.00  
% 3.63/1.00  fof(f21,plain,(
% 3.63/1.00    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.63/1.00    introduced(choice_axiom,[])).
% 3.63/1.00  
% 3.63/1.00  fof(f22,plain,(
% 3.63/1.00    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 3.63/1.00  
% 3.63/1.00  fof(f38,plain,(
% 3.63/1.00    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.63/1.00    inference(cnf_transformation,[],[f22])).
% 3.63/1.00  
% 3.63/1.00  fof(f2,axiom,(
% 3.63/1.00    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f24,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f2])).
% 3.63/1.00  
% 3.63/1.00  fof(f11,axiom,(
% 3.63/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f33,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f11])).
% 3.63/1.00  
% 3.63/1.00  fof(f45,plain,(
% 3.63/1.00    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.63/1.00    inference(definition_unfolding,[],[f38,f24,f33])).
% 3.63/1.00  
% 3.63/1.00  fof(f10,axiom,(
% 3.63/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f32,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.63/1.00    inference(cnf_transformation,[],[f10])).
% 3.63/1.00  
% 3.63/1.00  fof(f42,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.63/1.00    inference(definition_unfolding,[],[f32,f33])).
% 3.63/1.00  
% 3.63/1.00  fof(f5,axiom,(
% 3.63/1.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f27,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.63/1.00    inference(cnf_transformation,[],[f5])).
% 3.63/1.00  
% 3.63/1.00  fof(f40,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.63/1.00    inference(definition_unfolding,[],[f27,f33])).
% 3.63/1.00  
% 3.63/1.00  fof(f4,axiom,(
% 3.63/1.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f26,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.63/1.00    inference(cnf_transformation,[],[f4])).
% 3.63/1.00  
% 3.63/1.00  fof(f39,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 3.63/1.00    inference(definition_unfolding,[],[f26,f33])).
% 3.63/1.00  
% 3.63/1.00  cnf(c_5,plain,
% 3.63/1.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.63/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_9,plain,
% 3.63/1.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.63/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_0,plain,
% 3.63/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_641,plain,
% 3.63/1.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_681,plain,
% 3.63/1.00      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_5,c_641]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_13,negated_conjecture,
% 3.63/1.00      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 3.63/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_51,negated_conjecture,
% 3.63/1.00      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 3.63/1.00      inference(theory_normalisation,[status(thm)],[c_13,c_9,c_0]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4247,plain,
% 3.63/1.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
% 3.99/1.00      inference(demodulation,[status(thm)],[c_681,c_51]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_8,plain,
% 3.99/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.99/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_3,plain,
% 3.99/1.00      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.99/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_763,plain,
% 3.99/1.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_8,c_3]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2,plain,
% 3.99/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.99/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_650,plain,
% 3.99/1.00      ( k2_xboole_0(X0,X0) = X0 ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_682,plain,
% 3.99/1.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_650,c_641]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1032,plain,
% 3.99/1.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_0,c_682]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1293,plain,
% 3.99/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X0) ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_763,c_1032]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1331,plain,
% 3.99/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.99/1.00      inference(light_normalisation,[status(thm)],[c_1293,c_650]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1286,plain,
% 3.99/1.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_5,c_1032]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1342,plain,
% 3.99/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 3.99/1.00      inference(light_normalisation,[status(thm)],[c_1286,c_1032]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_4248,plain,
% 3.99/1.00      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 3.99/1.00      inference(demodulation,[status(thm)],[c_4247,c_1331,c_1342]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5023,plain,
% 3.99/1.00      ( $false ),
% 3.99/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4248,c_0]) ).
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  ------                               Statistics
% 3.99/1.00  
% 3.99/1.00  ------ Selected
% 3.99/1.00  
% 3.99/1.00  total_time:                             0.209
% 3.99/1.00  
%------------------------------------------------------------------------------
