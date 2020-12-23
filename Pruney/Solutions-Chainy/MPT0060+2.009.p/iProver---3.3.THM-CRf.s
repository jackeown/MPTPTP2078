%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:00 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f11,f14,f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f15,f14,f14])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
   => k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f16,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_105,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_4,negated_conjecture,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1133,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_105,c_4])).

cnf(c_9003,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2,c_1133])).

cnf(c_1,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_187,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9003,c_187])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.71/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.00  
% 3.71/1.00  ------  iProver source info
% 3.71/1.00  
% 3.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.00  git: non_committed_changes: false
% 3.71/1.00  git: last_make_outside_of_git: false
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  ------ Parsing...
% 3.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/1.00  ------ Proving...
% 3.71/1.00  ------ Problem Properties 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  clauses                                 5
% 3.71/1.00  conjectures                             1
% 3.71/1.00  EPR                                     0
% 3.71/1.00  Horn                                    5
% 3.71/1.00  unary                                   5
% 3.71/1.00  binary                                  0
% 3.71/1.00  lits                                    5
% 3.71/1.00  lits eq                                 5
% 3.71/1.00  fd_pure                                 0
% 3.71/1.00  fd_pseudo                               0
% 3.71/1.00  fd_cond                                 0
% 3.71/1.00  fd_pseudo_cond                          0
% 3.71/1.00  AC symbols                              0
% 3.71/1.00  
% 3.71/1.00  ------ Input Options Time Limit: Unbounded
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  Current options:
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ Proving...
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS status Theorem for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  fof(f3,axiom,(
% 3.71/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f13,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f3])).
% 3.71/1.00  
% 3.71/1.00  fof(f4,axiom,(
% 3.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f14,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f4])).
% 3.71/1.00  
% 3.71/1.00  fof(f18,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.71/1.00    inference(definition_unfolding,[],[f13,f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f1,axiom,(
% 3.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f11,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f1])).
% 3.71/1.00  
% 3.71/1.00  fof(f17,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.71/1.00    inference(definition_unfolding,[],[f11,f14,f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f5,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f15,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f5])).
% 3.71/1.00  
% 3.71/1.00  fof(f19,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f15,f14,f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f6,conjecture,(
% 3.71/1.00    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f7,negated_conjecture,(
% 3.71/1.00    ~! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.71/1.00    inference(negated_conjecture,[],[f6])).
% 3.71/1.00  
% 3.71/1.00  fof(f8,plain,(
% 3.71/1.00    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.71/1.00    inference(ennf_transformation,[],[f7])).
% 3.71/1.00  
% 3.71/1.00  fof(f9,plain,(
% 3.71/1.00    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) => k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f10,plain,(
% 3.71/1.00    k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f16,plain,(
% 3.71/1.00    k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 3.71/1.00    inference(cnf_transformation,[],[f10])).
% 3.71/1.00  
% 3.71/1.00  fof(f20,plain,(
% 3.71/1.00    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))),
% 3.71/1.00    inference(definition_unfolding,[],[f16,f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f2,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f12,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f2])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2,plain,
% 3.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f18]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_0,plain,
% 3.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f17]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3,plain,
% 3.71/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.71/1.00      inference(cnf_transformation,[],[f19]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_105,plain,
% 3.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4,negated_conjecture,
% 3.71/1.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
% 3.71/1.00      inference(cnf_transformation,[],[f20]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1133,plain,
% 3.71/1.00      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_105,c_4]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9003,plain,
% 3.71/1.00      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2,c_1133]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1,plain,
% 3.71/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f12]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_187,plain,
% 3.71/1.00      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,[status(thm)],[c_9003,c_187]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ Selected
% 3.71/1.00  
% 3.71/1.00  total_time:                             0.347
% 3.71/1.00  
%------------------------------------------------------------------------------
