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
% DateTime   : Thu Dec  3 11:22:39 EST 2020

% Result     : CounterSatisfiable 3.56s
% Output     : Saturation 3.56s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f7])).

fof(f10,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f8])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2)
   => k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f18,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_5,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:58:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.56/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.98  
% 3.56/0.98  ------  iProver source info
% 3.56/0.98  
% 3.56/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.98  git: non_committed_changes: false
% 3.56/0.98  git: last_make_outside_of_git: false
% 3.56/0.98  
% 3.56/0.98  ------ 
% 3.56/0.98  ------ Parsing...
% 3.56/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/0.98  ------ Proving...
% 3.56/0.98  ------ Problem Properties 
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  clauses                                 6
% 3.56/0.98  conjectures                             1
% 3.56/0.98  EPR                                     0
% 3.56/0.98  Horn                                    6
% 3.56/0.98  unary                                   6
% 3.56/0.98  binary                                  0
% 3.56/0.98  lits                                    6
% 3.56/0.98  lits eq                                 6
% 3.56/0.98  fd_pure                                 0
% 3.56/0.98  fd_pseudo                               0
% 3.56/0.98  fd_cond                                 0
% 3.56/0.98  fd_pseudo_cond                          0
% 3.56/0.98  AC symbols                              1
% 3.56/0.98  
% 3.56/0.98  ------ Input Options Time Limit: Unbounded
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.56/0.98  Current options:
% 3.56/0.98  ------ 
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  ------ Proving...
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  % SZS output start Saturation for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  fof(f7,conjecture,(
% 3.56/0.98    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f8,negated_conjecture,(
% 3.56/0.98    ~! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.56/0.98    inference(negated_conjecture,[],[f7])).
% 3.56/0.98  
% 3.56/0.98  fof(f10,plain,(
% 3.56/0.98    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.56/0.98    inference(ennf_transformation,[],[f8])).
% 3.56/0.98  
% 3.56/0.98  fof(f11,plain,(
% 3.56/0.98    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2) => k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f12,plain,(
% 3.56/0.98    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 3.56/0.98  
% 3.56/0.98  fof(f18,plain,(
% 3.56/0.98    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 3.56/0.98    inference(cnf_transformation,[],[f12])).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5,negated_conjecture,
% 3.56/0.98      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
% 3.56/0.98      inference(cnf_transformation,[],[f18]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_23,negated_conjecture,
% 3.56/0.98      ( ~ iProver_ARSWP_2 | arAF0_k2_xboole_0_0 != arAF0_k4_xboole_0_0 ),
% 3.56/0.98      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_77,plain,
% 3.56/0.98      ( arAF0_k2_xboole_0_0 != arAF0_k4_xboole_0_0
% 3.56/0.98      | iProver_ARSWP_2 != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  % SZS output end Saturation for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  ------                               Statistics
% 3.56/0.98  
% 3.56/0.98  ------ Selected
% 3.56/0.98  
% 3.56/0.98  total_time:                             0.033
% 3.56/0.98  
%------------------------------------------------------------------------------
