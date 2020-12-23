%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:39 EST 2020

% Result     : CounterSatisfiable 3.41s
% Output     : Saturation 3.41s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    7
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2)
   => k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f17,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_5,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_23,negated_conjecture,
    ( ~ iProver_ARSWP_2
    | arAF0_k2_xboole_0_0 != arAF0_k4_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_77,plain,
    ( arAF0_k2_xboole_0_0 != arAF0_k4_xboole_0_0
    | iProver_ARSWP_2 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:11:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.41/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/0.99  
% 3.41/0.99  ------  iProver source info
% 3.41/0.99  
% 3.41/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.41/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/0.99  git: non_committed_changes: false
% 3.41/0.99  git: last_make_outside_of_git: false
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  ------ Parsing...
% 3.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/0.99  ------ Proving...
% 3.41/0.99  ------ Problem Properties 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  clauses                                 6
% 3.41/0.99  conjectures                             1
% 3.41/0.99  EPR                                     0
% 3.41/0.99  Horn                                    6
% 3.41/0.99  unary                                   6
% 3.41/0.99  binary                                  0
% 3.41/0.99  lits                                    6
% 3.41/0.99  lits eq                                 6
% 3.41/0.99  fd_pure                                 0
% 3.41/0.99  fd_pseudo                               0
% 3.41/0.99  fd_cond                                 0
% 3.41/0.99  fd_pseudo_cond                          0
% 3.41/0.99  AC symbols                              1
% 3.41/0.99  
% 3.41/0.99  ------ Input Options Time Limit: Unbounded
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.41/0.99  Current options:
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ Proving...
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  % SZS output start Saturation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  fof(f7,conjecture,(
% 3.41/0.99    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f8,negated_conjecture,(
% 3.41/0.99    ~! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.41/0.99    inference(negated_conjecture,[],[f7])).
% 3.41/0.99  
% 3.41/0.99  fof(f9,plain,(
% 3.41/0.99    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.41/0.99    inference(ennf_transformation,[],[f8])).
% 3.41/0.99  
% 3.41/0.99  fof(f10,plain,(
% 3.41/0.99    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2) => k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f11,plain,(
% 3.41/0.99    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 3.41/0.99  
% 3.41/0.99  fof(f17,plain,(
% 3.41/0.99    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 3.41/0.99    inference(cnf_transformation,[],[f11])).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5,negated_conjecture,
% 3.41/0.99      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
% 3.41/0.99      inference(cnf_transformation,[],[f17]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_23,negated_conjecture,
% 3.41/0.99      ( ~ iProver_ARSWP_2 | arAF0_k2_xboole_0_0 != arAF0_k4_xboole_0_0 ),
% 3.41/0.99      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_77,plain,
% 3.41/0.99      ( arAF0_k2_xboole_0_0 != arAF0_k4_xboole_0_0
% 3.41/0.99      | iProver_ARSWP_2 != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS output end Saturation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  ------                               Statistics
% 3.41/0.99  
% 3.41/0.99  ------ Selected
% 3.41/0.99  
% 3.41/0.99  total_time:                             0.048
% 3.41/0.99  
%------------------------------------------------------------------------------
