%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:20 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   31 (  67 expanded)
%              Number of clauses        :   10 (  14 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  71 expanded)
%              Number of equality atoms :   33 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f107,plain,(
    ! [X0] : k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f77,f75])).

fof(f119,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f88,f107])).

fof(f15,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f108,plain,(
    ! [X0,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_tarski(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f114,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2) ),
    inference(definition_unfolding,[],[f83,f107,f107])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(negated_conjecture,[],[f27])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) != k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(ennf_transformation,[],[f28])).

fof(f56,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) != k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))
   => k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4),k4_tarski(sK2,sK3),k4_tarski(sK2,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4),k4_tarski(sK2,sK3),k4_tarski(sK2,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f56])).

fof(f106,plain,(
    k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4),k4_tarski(sK2,sK3),k4_tarski(sK2,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f57])).

fof(f128,plain,(
    k2_xboole_0(k2_tarski(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4)),k2_tarski(k4_tarski(sK2,sK3),k4_tarski(sK2,sK4))) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(definition_unfolding,[],[f106,f75])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_7791,plain,
    ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_28,c_0])).

cnf(c_23,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X1),k2_zfmisc_1(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)),X1)) = k2_zfmisc_1(k2_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_7802,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X0,X0),X1),k2_zfmisc_1(k2_tarski(X2,X2),X1)) = k2_zfmisc_1(k2_tarski(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_23,c_0])).

cnf(c_8293,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
    inference(superposition,[status(thm)],[c_7791,c_7802])).

cnf(c_8332,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_8293,c_7791])).

cnf(c_45,negated_conjecture,
    ( k2_xboole_0(k2_tarski(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4)),k2_tarski(k4_tarski(sK2,sK3),k4_tarski(sK2,sK4))) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_8810,plain,
    ( k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_8332,c_45])).

cnf(c_8893,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8810])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.96/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.00  
% 3.96/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/1.00  
% 3.96/1.00  ------  iProver source info
% 3.96/1.00  
% 3.96/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.96/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/1.00  git: non_committed_changes: false
% 3.96/1.00  git: last_make_outside_of_git: false
% 3.96/1.00  
% 3.96/1.00  ------ 
% 3.96/1.00  ------ Parsing...
% 3.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  ------ Proving...
% 3.96/1.00  ------ Problem Properties 
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  clauses                                 40
% 3.96/1.00  conjectures                             4
% 3.96/1.00  EPR                                     5
% 3.96/1.00  Horn                                    34
% 3.96/1.00  unary                                   23
% 3.96/1.00  binary                                  10
% 3.96/1.00  lits                                    69
% 3.96/1.00  lits eq                                 37
% 3.96/1.00  fd_pure                                 0
% 3.96/1.00  fd_pseudo                               0
% 3.96/1.00  fd_cond                                 0
% 3.96/1.00  fd_pseudo_cond                          7
% 3.96/1.00  AC symbols                              0
% 3.96/1.00  
% 3.96/1.00  ------ Input Options Time Limit: Unbounded
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing...
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.96/1.00  Current options:
% 3.96/1.00  ------ 
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing...
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  % SZS status Theorem for theBenchmark.p
% 3.96/1.00  
% 3.96/1.00   Resolution empty clause
% 3.96/1.00  
% 3.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/1.00  
% 3.96/1.00  fof(f21,axiom,(
% 3.96/1.00    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f88,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f21])).
% 3.96/1.00  
% 3.96/1.00  fof(f16,axiom,(
% 3.96/1.00    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f77,plain,(
% 3.96/1.00    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f16])).
% 3.96/1.00  
% 3.96/1.00  fof(f14,axiom,(
% 3.96/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f75,plain,(
% 3.96/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f14])).
% 3.96/1.00  
% 3.96/1.00  fof(f107,plain,(
% 3.96/1.00    ( ! [X0] : (k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k1_tarski(X0)) )),
% 3.96/1.00    inference(definition_unfolding,[],[f77,f75])).
% 3.96/1.00  
% 3.96/1.00  fof(f119,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X2))) )),
% 3.96/1.00    inference(definition_unfolding,[],[f88,f107])).
% 3.96/1.00  
% 3.96/1.00  fof(f15,axiom,(
% 3.96/1.00    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f76,plain,(
% 3.96/1.00    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f15])).
% 3.96/1.00  
% 3.96/1.00  fof(f108,plain,(
% 3.96/1.00    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)) )),
% 3.96/1.00    inference(definition_unfolding,[],[f76,f75])).
% 3.96/1.00  
% 3.96/1.00  fof(f18,axiom,(
% 3.96/1.00    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_tarski(X0,X1)) & k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f83,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f18])).
% 3.96/1.00  
% 3.96/1.00  fof(f114,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2)) )),
% 3.96/1.00    inference(definition_unfolding,[],[f83,f107,f107])).
% 3.96/1.00  
% 3.96/1.00  fof(f27,conjecture,(
% 3.96/1.00    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f28,negated_conjecture,(
% 3.96/1.00    ~! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.96/1.00    inference(negated_conjecture,[],[f27])).
% 3.96/1.00  
% 3.96/1.00  fof(f42,plain,(
% 3.96/1.00    ? [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) != k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.96/1.00    inference(ennf_transformation,[],[f28])).
% 3.96/1.00  
% 3.96/1.00  fof(f56,plain,(
% 3.96/1.00    ? [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) != k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) => k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4),k4_tarski(sK2,sK3),k4_tarski(sK2,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f57,plain,(
% 3.96/1.00    k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4),k4_tarski(sK2,sK3),k4_tarski(sK2,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f56])).
% 3.96/1.00  
% 3.96/1.00  fof(f106,plain,(
% 3.96/1.00    k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4),k4_tarski(sK2,sK3),k4_tarski(sK2,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.96/1.00    inference(cnf_transformation,[],[f57])).
% 3.96/1.00  
% 3.96/1.00  fof(f128,plain,(
% 3.96/1.00    k2_xboole_0(k2_tarski(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4)),k2_tarski(k4_tarski(sK2,sK3),k4_tarski(sK2,sK4))) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.96/1.00    inference(definition_unfolding,[],[f106,f75])).
% 3.96/1.00  
% 3.96/1.00  cnf(c_28,plain,
% 3.96/1.00      ( k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
% 3.96/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_0,plain,
% 3.96/1.00      ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
% 3.96/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_7791,plain,
% 3.96/1.00      ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
% 3.96/1.00      inference(demodulation,[status(thm)],[c_28,c_0]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_23,plain,
% 3.96/1.00      ( k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X1),k2_zfmisc_1(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)),X1)) = k2_zfmisc_1(k2_tarski(X0,X2),X1) ),
% 3.96/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_7802,plain,
% 3.96/1.00      ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X0,X0),X1),k2_zfmisc_1(k2_tarski(X2,X2),X1)) = k2_zfmisc_1(k2_tarski(X0,X2),X1) ),
% 3.96/1.00      inference(demodulation,[status(thm)],[c_23,c_0]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_8293,plain,
% 3.96/1.00      ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_7791,c_7802]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_8332,plain,
% 3.96/1.00      ( k2_xboole_0(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
% 3.96/1.00      inference(light_normalisation,[status(thm)],[c_8293,c_7791]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_45,negated_conjecture,
% 3.96/1.00      ( k2_xboole_0(k2_tarski(k4_tarski(sK1,sK3),k4_tarski(sK1,sK4)),k2_tarski(k4_tarski(sK2,sK3),k4_tarski(sK2,sK4))) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
% 3.96/1.00      inference(cnf_transformation,[],[f128]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_8810,plain,
% 3.96/1.00      ( k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
% 3.96/1.00      inference(demodulation,[status(thm)],[c_8332,c_45]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_8893,plain,
% 3.96/1.00      ( $false ),
% 3.96/1.00      inference(equality_resolution_simp,[status(thm)],[c_8810]) ).
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/1.00  
% 3.96/1.00  ------                               Statistics
% 3.96/1.00  
% 3.96/1.00  ------ Selected
% 3.96/1.00  
% 3.96/1.00  total_time:                             0.377
% 3.96/1.00  
%------------------------------------------------------------------------------
