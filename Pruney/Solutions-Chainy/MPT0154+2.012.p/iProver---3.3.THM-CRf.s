%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:53 EST 2020

% Result     : Theorem 31.66s
% Output     : CNFRefutation 31.66s
% Verified   : 
% Statistics : Number of formulae       :   32 (  86 expanded)
%              Number of clauses        :    8 (  10 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   33 (  87 expanded)
%              Number of equality atoms :   32 (  86 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f53,f62])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f53,f62,f62])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f57,f53,f64,f63])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f18])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f33])).

fof(f61,plain,(
    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f61,f62,f64])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_18,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1004,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(superposition,[status(thm)],[c_1,c_18])).

cnf(c_63404,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(superposition,[status(thm)],[c_1,c_1004])).

cnf(c_63591,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(demodulation,[status(thm)],[c_63404,c_1])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_83305,plain,
    ( k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) ),
    inference(demodulation,[status(thm)],[c_63591,c_20])).

cnf(c_83307,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_83305])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:13:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 31.66/4.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.66/4.48  
% 31.66/4.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.66/4.48  
% 31.66/4.48  ------  iProver source info
% 31.66/4.48  
% 31.66/4.48  git: date: 2020-06-30 10:37:57 +0100
% 31.66/4.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.66/4.48  git: non_committed_changes: false
% 31.66/4.48  git: last_make_outside_of_git: false
% 31.66/4.48  
% 31.66/4.48  ------ 
% 31.66/4.48  ------ Parsing...
% 31.66/4.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.66/4.48  ------ Proving...
% 31.66/4.48  ------ Problem Properties 
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  clauses                                 20
% 31.66/4.48  conjectures                             2
% 31.66/4.48  EPR                                     3
% 31.66/4.48  Horn                                    15
% 31.66/4.48  unary                                   10
% 31.66/4.48  binary                                  4
% 31.66/4.48  lits                                    37
% 31.66/4.48  lits eq                                 13
% 31.66/4.48  fd_pure                                 0
% 31.66/4.48  fd_pseudo                               0
% 31.66/4.48  fd_cond                                 0
% 31.66/4.48  fd_pseudo_cond                          4
% 31.66/4.48  AC symbols                              0
% 31.66/4.48  
% 31.66/4.48  ------ Input Options Time Limit: Unbounded
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing...
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 31.66/4.48  Current options:
% 31.66/4.48  ------ 
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  ------ Proving...
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing...
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.66/4.48  
% 31.66/4.48  ------ Proving...
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing...
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.66/4.48  
% 31.66/4.48  ------ Proving...
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.66/4.48  
% 31.66/4.48  ------ Proving...
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.66/4.48  
% 31.66/4.48  ------ Proving...
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.66/4.48  
% 31.66/4.48  ------ Proving...
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  % SZS status Theorem for theBenchmark.p
% 31.66/4.48  
% 31.66/4.48   Resolution empty clause
% 31.66/4.48  
% 31.66/4.48  % SZS output start CNFRefutation for theBenchmark.p
% 31.66/4.48  
% 31.66/4.48  fof(f17,axiom,(
% 31.66/4.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.66/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.48  
% 31.66/4.48  fof(f60,plain,(
% 31.66/4.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.66/4.48    inference(cnf_transformation,[],[f17])).
% 31.66/4.48  
% 31.66/4.48  fof(f12,axiom,(
% 31.66/4.48    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 31.66/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.48  
% 31.66/4.48  fof(f55,plain,(
% 31.66/4.48    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 31.66/4.48    inference(cnf_transformation,[],[f12])).
% 31.66/4.48  
% 31.66/4.48  fof(f10,axiom,(
% 31.66/4.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 31.66/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.48  
% 31.66/4.48  fof(f53,plain,(
% 31.66/4.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 31.66/4.48    inference(cnf_transformation,[],[f10])).
% 31.66/4.48  
% 31.66/4.48  fof(f62,plain,(
% 31.66/4.48    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 31.66/4.48    inference(definition_unfolding,[],[f55,f53])).
% 31.66/4.48  
% 31.66/4.48  fof(f67,plain,(
% 31.66/4.48    ( ! [X0] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0)) )),
% 31.66/4.48    inference(definition_unfolding,[],[f60,f62])).
% 31.66/4.48  
% 31.66/4.48  fof(f14,axiom,(
% 31.66/4.48    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 31.66/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.48  
% 31.66/4.48  fof(f57,plain,(
% 31.66/4.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 31.66/4.48    inference(cnf_transformation,[],[f14])).
% 31.66/4.48  
% 31.66/4.48  fof(f13,axiom,(
% 31.66/4.48    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 31.66/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.48  
% 31.66/4.48  fof(f56,plain,(
% 31.66/4.48    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 31.66/4.48    inference(cnf_transformation,[],[f13])).
% 31.66/4.48  
% 31.66/4.48  fof(f64,plain,(
% 31.66/4.48    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 31.66/4.48    inference(definition_unfolding,[],[f56,f53,f62])).
% 31.66/4.48  
% 31.66/4.48  fof(f11,axiom,(
% 31.66/4.48    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 31.66/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.48  
% 31.66/4.48  fof(f54,plain,(
% 31.66/4.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 31.66/4.48    inference(cnf_transformation,[],[f11])).
% 31.66/4.48  
% 31.66/4.48  fof(f63,plain,(
% 31.66/4.48    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k2_enumset1(X0,X1,X2,X3)) )),
% 31.66/4.48    inference(definition_unfolding,[],[f54,f53,f62,f62])).
% 31.66/4.48  
% 31.66/4.48  fof(f70,plain,(
% 31.66/4.48    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 31.66/4.48    inference(definition_unfolding,[],[f57,f53,f64,f63])).
% 31.66/4.48  
% 31.66/4.48  fof(f18,conjecture,(
% 31.66/4.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.66/4.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.48  
% 31.66/4.48  fof(f19,negated_conjecture,(
% 31.66/4.48    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.66/4.48    inference(negated_conjecture,[],[f18])).
% 31.66/4.48  
% 31.66/4.48  fof(f21,plain,(
% 31.66/4.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 31.66/4.48    inference(ennf_transformation,[],[f19])).
% 31.66/4.48  
% 31.66/4.48  fof(f33,plain,(
% 31.66/4.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3)),
% 31.66/4.48    introduced(choice_axiom,[])).
% 31.66/4.48  
% 31.66/4.48  fof(f34,plain,(
% 31.66/4.48    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3)),
% 31.66/4.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f33])).
% 31.66/4.48  
% 31.66/4.48  fof(f61,plain,(
% 31.66/4.48    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3)),
% 31.66/4.48    inference(cnf_transformation,[],[f34])).
% 31.66/4.48  
% 31.66/4.48  fof(f72,plain,(
% 31.66/4.48    k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK2)))),
% 31.66/4.48    inference(definition_unfolding,[],[f61,f62,f64])).
% 31.66/4.48  
% 31.66/4.48  cnf(c_1,plain,
% 31.66/4.48      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0) ),
% 31.66/4.48      inference(cnf_transformation,[],[f67]) ).
% 31.66/4.48  
% 31.66/4.48  cnf(c_18,plain,
% 31.66/4.48      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
% 31.66/4.48      inference(cnf_transformation,[],[f70]) ).
% 31.66/4.48  
% 31.66/4.48  cnf(c_1004,plain,
% 31.66/4.48      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
% 31.66/4.48      inference(superposition,[status(thm)],[c_1,c_18]) ).
% 31.66/4.48  
% 31.66/4.48  cnf(c_63404,plain,
% 31.66/4.48      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X1))),k1_tarski(X0))) ),
% 31.66/4.48      inference(superposition,[status(thm)],[c_1,c_1004]) ).
% 31.66/4.48  
% 31.66/4.48  cnf(c_63591,plain,
% 31.66/4.48      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
% 31.66/4.48      inference(demodulation,[status(thm)],[c_63404,c_1]) ).
% 31.66/4.48  
% 31.66/4.48  cnf(c_20,negated_conjecture,
% 31.66/4.48      ( k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK2))) ),
% 31.66/4.48      inference(cnf_transformation,[],[f72]) ).
% 31.66/4.48  
% 31.66/4.48  cnf(c_83305,plain,
% 31.66/4.48      ( k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))) ),
% 31.66/4.48      inference(demodulation,[status(thm)],[c_63591,c_20]) ).
% 31.66/4.48  
% 31.66/4.48  cnf(c_83307,plain,
% 31.66/4.48      ( $false ),
% 31.66/4.48      inference(equality_resolution_simp,[status(thm)],[c_83305]) ).
% 31.66/4.48  
% 31.66/4.48  
% 31.66/4.48  % SZS output end CNFRefutation for theBenchmark.p
% 31.66/4.48  
% 31.66/4.48  ------                               Statistics
% 31.66/4.48  
% 31.66/4.48  ------ Selected
% 31.66/4.48  
% 31.66/4.48  total_time:                             3.718
% 31.66/4.48  
%------------------------------------------------------------------------------
