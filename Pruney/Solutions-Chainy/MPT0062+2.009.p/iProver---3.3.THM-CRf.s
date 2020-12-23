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
% DateTime   : Thu Dec  3 11:23:02 EST 2020

% Result     : Theorem 35.56s
% Output     : CNFRefutation 35.56s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  39 expanded)
%              Number of equality atoms :   35 (  38 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,
    ( ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f38,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_117906,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_118122,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k3_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X2),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_8])).

cnf(c_125649,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_117906,c_118122])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_143153,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_125649,c_14])).

cnf(c_54,plain,
    ( X0 != X1
    | X2 != X3
    | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_1562,plain,
    ( k4_xboole_0(sK1,sK0) != X0
    | k4_xboole_0(sK0,sK1) != X1
    | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(X1,X0) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_1615,plain,
    ( k4_xboole_0(sK1,sK0) != X0
    | k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_1616,plain,
    ( k4_xboole_0(sK1,sK0) != X0
    | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_1615])).

cnf(c_1626,plain,
    ( k4_xboole_0(sK1,sK0) != k4_xboole_0(sK1,sK0)
    | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_1627,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1626])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143153,c_1627])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:33:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.56/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.56/4.99  
% 35.56/4.99  ------  iProver source info
% 35.56/4.99  
% 35.56/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.56/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.56/4.99  git: non_committed_changes: false
% 35.56/4.99  git: last_make_outside_of_git: false
% 35.56/4.99  
% 35.56/4.99  ------ 
% 35.56/4.99  ------ Parsing...
% 35.56/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  ------ Proving...
% 35.56/4.99  ------ Problem Properties 
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  clauses                                 15
% 35.56/4.99  conjectures                             1
% 35.56/4.99  EPR                                     0
% 35.56/4.99  Horn                                    15
% 35.56/4.99  unary                                   12
% 35.56/4.99  binary                                  3
% 35.56/4.99  lits                                    18
% 35.56/4.99  lits eq                                 16
% 35.56/4.99  fd_pure                                 0
% 35.56/4.99  fd_pseudo                               0
% 35.56/4.99  fd_cond                                 1
% 35.56/4.99  fd_pseudo_cond                          0
% 35.56/4.99  AC symbols                              0
% 35.56/4.99  
% 35.56/4.99  ------ Input Options Time Limit: Unbounded
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing...
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 35.56/4.99  Current options:
% 35.56/4.99  ------ 
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  % SZS status Theorem for theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  fof(f1,axiom,(
% 35.56/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.56/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f24,plain,(
% 35.56/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f1])).
% 35.56/4.99  
% 35.56/4.99  fof(f11,axiom,(
% 35.56/4.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.56/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f34,plain,(
% 35.56/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.56/4.99    inference(cnf_transformation,[],[f11])).
% 35.56/4.99  
% 35.56/4.99  fof(f9,axiom,(
% 35.56/4.99    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 35.56/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f32,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f9])).
% 35.56/4.99  
% 35.56/4.99  fof(f15,conjecture,(
% 35.56/4.99    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 35.56/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f16,negated_conjecture,(
% 35.56/4.99    ~! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 35.56/4.99    inference(negated_conjecture,[],[f15])).
% 35.56/4.99  
% 35.56/4.99  fof(f21,plain,(
% 35.56/4.99    ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 35.56/4.99    inference(ennf_transformation,[],[f16])).
% 35.56/4.99  
% 35.56/4.99  fof(f22,plain,(
% 35.56/4.99    ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 35.56/4.99    introduced(choice_axiom,[])).
% 35.56/4.99  
% 35.56/4.99  fof(f23,plain,(
% 35.56/4.99    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 35.56/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 35.56/4.99  
% 35.56/4.99  fof(f38,plain,(
% 35.56/4.99    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 35.56/4.99    inference(cnf_transformation,[],[f23])).
% 35.56/4.99  
% 35.56/4.99  cnf(c_0,plain,
% 35.56/4.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.56/4.99      inference(cnf_transformation,[],[f24]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_10,plain,
% 35.56/4.99      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 35.56/4.99      inference(cnf_transformation,[],[f34]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_117906,plain,
% 35.56/4.99      ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 35.56/4.99      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_8,plain,
% 35.56/4.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 35.56/4.99      inference(cnf_transformation,[],[f32]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_118122,plain,
% 35.56/4.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k3_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X2),k3_xboole_0(X0,X1)) ),
% 35.56/4.99      inference(superposition,[status(thm)],[c_10,c_8]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_125649,plain,
% 35.56/4.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 35.56/4.99      inference(superposition,[status(thm)],[c_117906,c_118122]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_14,negated_conjecture,
% 35.56/4.99      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
% 35.56/4.99      inference(cnf_transformation,[],[f38]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_143153,plain,
% 35.56/4.99      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
% 35.56/4.99      inference(demodulation,[status(thm)],[c_125649,c_14]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_54,plain,
% 35.56/4.99      ( X0 != X1 | X2 != X3 | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X3) ),
% 35.56/4.99      theory(equality) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1562,plain,
% 35.56/4.99      ( k4_xboole_0(sK1,sK0) != X0
% 35.56/4.99      | k4_xboole_0(sK0,sK1) != X1
% 35.56/4.99      | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(X1,X0) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_54]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1615,plain,
% 35.56/4.99      ( k4_xboole_0(sK1,sK0) != X0
% 35.56/4.99      | k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
% 35.56/4.99      | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_1562]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1616,plain,
% 35.56/4.99      ( k4_xboole_0(sK1,sK0) != X0
% 35.56/4.99      | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
% 35.56/4.99      inference(equality_resolution_simp,[status(thm)],[c_1615]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1626,plain,
% 35.56/4.99      ( k4_xboole_0(sK1,sK0) != k4_xboole_0(sK1,sK0)
% 35.56/4.99      | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_1616]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1627,plain,
% 35.56/4.99      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
% 35.56/4.99      inference(equality_resolution_simp,[status(thm)],[c_1626]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(contradiction,plain,
% 35.56/4.99      ( $false ),
% 35.56/4.99      inference(minisat,[status(thm)],[c_143153,c_1627]) ).
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  ------                               Statistics
% 35.56/4.99  
% 35.56/4.99  ------ Selected
% 35.56/4.99  
% 35.56/4.99  total_time:                             4.167
% 35.56/4.99  
%------------------------------------------------------------------------------
