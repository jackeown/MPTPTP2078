%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:52 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   35 (  78 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  91 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f23,f22,f31,f31])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f24,f37,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

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

fof(f49,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_28,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X3_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X2_38),k1_enumset1(X0_38,X0_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_320,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_33,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_163,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) != X0_36
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != X0_36
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_319,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,plain,
    ( k5_xboole_0(X0_36,k4_xboole_0(X1_36,X0_36)) = k5_xboole_0(X1_36,k4_xboole_0(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_198,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_120,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_95,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != X0_36
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != X0_36
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_119,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_320,c_319,c_198,c_120,c_119,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:21:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 2.31/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.31/1.00  
% 2.31/1.00  ------  iProver source info
% 2.31/1.00  
% 2.31/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.31/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.31/1.00  git: non_committed_changes: false
% 2.31/1.00  git: last_make_outside_of_git: false
% 2.31/1.00  
% 2.31/1.00  ------ 
% 2.31/1.00  ------ Parsing...
% 2.31/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.31/1.00  ------ Proving...
% 2.31/1.00  ------ Problem Properties 
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  clauses                                 10
% 2.31/1.00  conjectures                             1
% 2.31/1.00  EPR                                     0
% 2.31/1.00  Horn                                    10
% 2.31/1.00  unary                                   10
% 2.31/1.00  binary                                  0
% 2.31/1.00  lits                                    10
% 2.31/1.00  lits eq                                 10
% 2.31/1.00  fd_pure                                 0
% 2.31/1.00  fd_pseudo                               0
% 2.31/1.00  fd_cond                                 0
% 2.31/1.00  fd_pseudo_cond                          0
% 2.31/1.00  AC symbols                              0
% 2.31/1.00  
% 2.31/1.00  ------ Input Options Time Limit: Unbounded
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  ------ 
% 2.31/1.00  Current options:
% 2.31/1.00  ------ 
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  ------ Proving...
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  % SZS status Theorem for theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  fof(f4,axiom,(
% 2.31/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 2.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f24,plain,(
% 2.31/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f4])).
% 2.31/1.00  
% 2.31/1.00  fof(f3,axiom,(
% 2.31/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f23,plain,(
% 2.31/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f3])).
% 2.31/1.00  
% 2.31/1.00  fof(f2,axiom,(
% 2.31/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f22,plain,(
% 2.31/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.31/1.00    inference(cnf_transformation,[],[f2])).
% 2.31/1.00  
% 2.31/1.00  fof(f11,axiom,(
% 2.31/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f31,plain,(
% 2.31/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f11])).
% 2.31/1.00  
% 2.31/1.00  fof(f37,plain,(
% 2.31/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.31/1.00    inference(definition_unfolding,[],[f23,f22,f31,f31])).
% 2.31/1.00  
% 2.31/1.00  fof(f42,plain,(
% 2.31/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)))) )),
% 2.31/1.00    inference(definition_unfolding,[],[f24,f37,f37])).
% 2.31/1.00  
% 2.31/1.00  fof(f1,axiom,(
% 2.31/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f21,plain,(
% 2.31/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f1])).
% 2.31/1.00  
% 2.31/1.00  fof(f41,plain,(
% 2.31/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 2.31/1.00    inference(definition_unfolding,[],[f21,f22,f22])).
% 2.31/1.00  
% 2.31/1.00  fof(f16,conjecture,(
% 2.31/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f17,negated_conjecture,(
% 2.31/1.00    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.31/1.00    inference(negated_conjecture,[],[f16])).
% 2.31/1.00  
% 2.31/1.00  fof(f18,plain,(
% 2.31/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 2.31/1.00    inference(ennf_transformation,[],[f17])).
% 2.31/1.00  
% 2.31/1.00  fof(f19,plain,(
% 2.31/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.31/1.00    introduced(choice_axiom,[])).
% 2.31/1.00  
% 2.31/1.00  fof(f20,plain,(
% 2.31/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.31/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 2.31/1.00  
% 2.31/1.00  fof(f36,plain,(
% 2.31/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.31/1.00    inference(cnf_transformation,[],[f20])).
% 2.31/1.00  
% 2.31/1.00  fof(f49,plain,(
% 2.31/1.00    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))),
% 2.31/1.00    inference(definition_unfolding,[],[f36,f37,f37])).
% 2.31/1.00  
% 2.31/1.00  cnf(c_2,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
% 2.31/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_28,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X3_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X2_38),k1_enumset1(X0_38,X0_38,X1_38))) ),
% 2.31/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_320,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_33,plain,
% 2.31/1.00      ( X0_36 != X1_36 | X2_36 != X1_36 | X2_36 = X0_36 ),
% 2.31/1.00      theory(equality) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_163,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) != X0_36
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != X0_36
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_319,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_163]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1,plain,
% 2.31/1.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 2.31/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_29,plain,
% 2.31/1.00      ( k5_xboole_0(X0_36,k4_xboole_0(X1_36,X0_36)) = k5_xboole_0(X1_36,k4_xboole_0(X0_36,X1_36)) ),
% 2.31/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_198,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_29]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_120,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_29]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_95,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != X0_36
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != X0_36
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_119,plain,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
% 2.31/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_95]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_9,negated_conjecture,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
% 2.31/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_21,negated_conjecture,
% 2.31/1.00      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
% 2.31/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(contradiction,plain,
% 2.31/1.00      ( $false ),
% 2.31/1.00      inference(minisat,
% 2.31/1.00                [status(thm)],
% 2.31/1.00                [c_320,c_319,c_198,c_120,c_119,c_21]) ).
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  ------                               Statistics
% 2.31/1.00  
% 2.31/1.00  ------ Selected
% 2.31/1.00  
% 2.31/1.00  total_time:                             0.046
% 2.31/1.00  
%------------------------------------------------------------------------------
