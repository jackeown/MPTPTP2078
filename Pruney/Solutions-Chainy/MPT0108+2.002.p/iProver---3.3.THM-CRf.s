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
% DateTime   : Thu Dec  3 11:25:28 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 113 expanded)
%              Number of clauses        :   24 (  36 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   55 ( 114 expanded)
%              Number of equality atoms :   54 ( 113 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f26])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f37,f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f15,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f16])).

fof(f20,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f36,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f36,f26,f37])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f29,f37])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_33,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_1,c_5,c_2])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_32,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_6,c_5,c_2])).

cnf(c_2742,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_32])).

cnf(c_4484,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_33,c_2742])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_12,c_5,c_2])).

cnf(c_2511,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10,c_29])).

cnf(c_5954,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4484,c_2511])).

cnf(c_6121,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_10,c_5954])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2323,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_2])).

cnf(c_2839,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_2323])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_31,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_7,c_5,c_2])).

cnf(c_2333,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_3095,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_31,c_2333])).

cnf(c_3123,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2839,c_3095])).

cnf(c_6122,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6121,c_3123])).

cnf(c_6123,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6122])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:32:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.53/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/0.97  
% 3.53/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.97  
% 3.53/0.97  ------  iProver source info
% 3.53/0.97  
% 3.53/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.97  git: non_committed_changes: false
% 3.53/0.97  git: last_make_outside_of_git: false
% 3.53/0.97  
% 3.53/0.97  ------ 
% 3.53/0.97  ------ Parsing...
% 3.53/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.53/0.97  ------ Proving...
% 3.53/0.97  ------ Problem Properties 
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  clauses                                 13
% 3.53/0.97  conjectures                             1
% 3.53/0.97  EPR                                     0
% 3.53/0.97  Horn                                    13
% 3.53/0.97  unary                                   13
% 3.53/0.97  binary                                  0
% 3.53/0.97  lits                                    13
% 3.53/0.97  lits eq                                 13
% 3.53/0.97  fd_pure                                 0
% 3.53/0.97  fd_pseudo                               0
% 3.53/0.97  fd_cond                                 0
% 3.53/0.97  fd_pseudo_cond                          0
% 3.53/0.97  AC symbols                              1
% 3.53/0.97  
% 3.53/0.97  ------ Input Options Time Limit: Unbounded
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing...
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.53/0.97  Current options:
% 3.53/0.97  ------ 
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Proving...
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing...
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.97  
% 3.53/0.97  ------ Proving...
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.53/0.97  
% 3.53/0.97  ------ Proving...
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.97  
% 3.53/0.97  ------ Proving...
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.53/0.97  
% 3.53/0.97  ------ Proving...
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.97  
% 3.53/0.97  ------ Proving...
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.53/0.97  
% 3.53/0.97  ------ Proving...
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  % SZS status Theorem for theBenchmark.p
% 3.53/0.97  
% 3.53/0.97   Resolution empty clause
% 3.53/0.97  
% 3.53/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.97  
% 3.53/0.97  fof(f12,axiom,(
% 3.53/0.97    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f33,plain,(
% 3.53/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.53/0.97    inference(cnf_transformation,[],[f12])).
% 3.53/0.97  
% 3.53/0.97  fof(f1,axiom,(
% 3.53/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f22,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.53/0.97    inference(cnf_transformation,[],[f1])).
% 3.53/0.97  
% 3.53/0.97  fof(f14,axiom,(
% 3.53/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f35,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.53/0.97    inference(cnf_transformation,[],[f14])).
% 3.53/0.97  
% 3.53/0.97  fof(f5,axiom,(
% 3.53/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f26,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.53/0.97    inference(cnf_transformation,[],[f5])).
% 3.53/0.97  
% 3.53/0.97  fof(f37,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.53/0.97    inference(definition_unfolding,[],[f35,f26])).
% 3.53/0.97  
% 3.53/0.97  fof(f39,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.53/0.97    inference(definition_unfolding,[],[f22,f37,f37])).
% 3.53/0.97  
% 3.53/0.97  fof(f6,axiom,(
% 3.53/0.97    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f27,plain,(
% 3.53/0.97    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.53/0.97    inference(cnf_transformation,[],[f6])).
% 3.53/0.97  
% 3.53/0.97  fof(f2,axiom,(
% 3.53/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f23,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.53/0.97    inference(cnf_transformation,[],[f2])).
% 3.53/0.97  
% 3.53/0.97  fof(f7,axiom,(
% 3.53/0.97    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f28,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.53/0.97    inference(cnf_transformation,[],[f7])).
% 3.53/0.97  
% 3.53/0.97  fof(f41,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 3.53/0.97    inference(definition_unfolding,[],[f28,f37])).
% 3.53/0.97  
% 3.53/0.97  fof(f15,conjecture,(
% 3.53/0.97    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f16,negated_conjecture,(
% 3.53/0.97    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 3.53/0.97    inference(negated_conjecture,[],[f15])).
% 3.53/0.97  
% 3.53/0.97  fof(f19,plain,(
% 3.53/0.97    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 3.53/0.97    inference(ennf_transformation,[],[f16])).
% 3.53/0.97  
% 3.53/0.97  fof(f20,plain,(
% 3.53/0.97    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 3.53/0.97    introduced(choice_axiom,[])).
% 3.53/0.97  
% 3.53/0.97  fof(f21,plain,(
% 3.53/0.97    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 3.53/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 3.53/0.97  
% 3.53/0.97  fof(f36,plain,(
% 3.53/0.97    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 3.53/0.97    inference(cnf_transformation,[],[f21])).
% 3.53/0.97  
% 3.53/0.97  fof(f45,plain,(
% 3.53/0.97    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 3.53/0.97    inference(definition_unfolding,[],[f36,f26,f37])).
% 3.53/0.97  
% 3.53/0.97  fof(f4,axiom,(
% 3.53/0.97    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f18,plain,(
% 3.53/0.97    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.53/0.97    inference(rectify,[],[f4])).
% 3.53/0.97  
% 3.53/0.97  fof(f25,plain,(
% 3.53/0.97    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.53/0.97    inference(cnf_transformation,[],[f18])).
% 3.53/0.97  
% 3.53/0.97  fof(f8,axiom,(
% 3.53/0.97    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.97  
% 3.53/0.97  fof(f29,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.53/0.97    inference(cnf_transformation,[],[f8])).
% 3.53/0.97  
% 3.53/0.97  fof(f42,plain,(
% 3.53/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 3.53/0.97    inference(definition_unfolding,[],[f29,f37])).
% 3.53/0.97  
% 3.53/0.97  cnf(c_10,plain,
% 3.53/0.97      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.53/0.97      inference(cnf_transformation,[],[f33]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_1,plain,
% 3.53/0.97      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.53/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_5,plain,
% 3.53/0.97      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.53/0.97      inference(cnf_transformation,[],[f27]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_2,plain,
% 3.53/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.53/0.97      inference(cnf_transformation,[],[f23]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_33,plain,
% 3.53/0.97      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.53/0.97      inference(theory_normalisation,[status(thm)],[c_1,c_5,c_2]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_6,plain,
% 3.53/0.97      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 3.53/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_32,plain,
% 3.53/0.97      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 3.53/0.97      inference(theory_normalisation,[status(thm)],[c_6,c_5,c_2]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_2742,plain,
% 3.53/0.97      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 3.53/0.97      inference(superposition,[status(thm)],[c_2,c_32]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_4484,plain,
% 3.53/0.97      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 3.53/0.97      inference(superposition,[status(thm)],[c_33,c_2742]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_12,negated_conjecture,
% 3.53/0.97      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 3.53/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_29,negated_conjecture,
% 3.53/0.97      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
% 3.53/0.97      inference(theory_normalisation,[status(thm)],[c_12,c_5,c_2]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_2511,plain,
% 3.53/0.97      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
% 3.53/0.97      inference(demodulation,[status(thm)],[c_10,c_29]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_5954,plain,
% 3.53/0.97      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
% 3.53/0.97      inference(demodulation,[status(thm)],[c_4484,c_2511]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_6121,plain,
% 3.53/0.97      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
% 3.53/0.97      inference(superposition,[status(thm)],[c_10,c_5954]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_4,plain,
% 3.53/0.97      ( k3_xboole_0(X0,X0) = X0 ),
% 3.53/0.97      inference(cnf_transformation,[],[f25]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_2323,plain,
% 3.53/0.97      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 3.53/0.97      inference(superposition,[status(thm)],[c_5,c_2]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_2839,plain,
% 3.53/0.97      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 3.53/0.97      inference(superposition,[status(thm)],[c_4,c_2323]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_7,plain,
% 3.53/0.97      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 3.53/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_31,plain,
% 3.53/0.97      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 3.53/0.97      inference(theory_normalisation,[status(thm)],[c_7,c_5,c_2]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_2333,plain,
% 3.53/0.97      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.53/0.97      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_3095,plain,
% 3.53/0.97      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
% 3.53/0.97      inference(light_normalisation,[status(thm)],[c_31,c_2333]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_3123,plain,
% 3.53/0.97      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = X0 ),
% 3.53/0.97      inference(superposition,[status(thm)],[c_2839,c_3095]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_6122,plain,
% 3.53/0.97      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 3.53/0.97      inference(demodulation,[status(thm)],[c_6121,c_3123]) ).
% 3.53/0.97  
% 3.53/0.97  cnf(c_6123,plain,
% 3.53/0.97      ( $false ),
% 3.53/0.97      inference(equality_resolution_simp,[status(thm)],[c_6122]) ).
% 3.53/0.97  
% 3.53/0.97  
% 3.53/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.97  
% 3.53/0.97  ------                               Statistics
% 3.53/0.97  
% 3.53/0.97  ------ Selected
% 3.53/0.97  
% 3.53/0.97  total_time:                             0.24
% 3.53/0.97  
%------------------------------------------------------------------------------
