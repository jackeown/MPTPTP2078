%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:14 EST 2020

% Result     : Theorem 39.86s
% Output     : CNFRefutation 39.86s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 213 expanded)
%              Number of clauses        :   29 (  53 expanded)
%              Number of leaves         :    9 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 246 expanded)
%              Number of equality atoms :   55 ( 213 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21])).

fof(f37,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f32,f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f33,f32,f32])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f36,f32])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_147230,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_147232,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_147357,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_147230,c_147232])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_147376,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_150068,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_147357,c_147376])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_147301,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_147393,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_9,c_147301])).

cnf(c_147398,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_147393,c_9])).

cnf(c_166144,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_150068,c_147398])).

cnf(c_166530,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,sK2) ),
    inference(demodulation,[status(thm)],[c_166144,c_147301,c_150068])).

cnf(c_166674,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_166530])).

cnf(c_7413,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_7296,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_9066,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7413,c_7296])).

cnf(c_9316,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_9066,c_9])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7304,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_13282,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_9316,c_7304])).

cnf(c_13300,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_13282,c_9])).

cnf(c_13301,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_13300,c_0])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7266,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) != k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_12,c_9])).

cnf(c_145526,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_13301,c_7266])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_166674,c_145526])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 39.86/5.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.86/5.48  
% 39.86/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.86/5.48  
% 39.86/5.48  ------  iProver source info
% 39.86/5.48  
% 39.86/5.48  git: date: 2020-06-30 10:37:57 +0100
% 39.86/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.86/5.48  git: non_committed_changes: false
% 39.86/5.48  git: last_make_outside_of_git: false
% 39.86/5.48  
% 39.86/5.48  ------ 
% 39.86/5.48  ------ Parsing...
% 39.86/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  ------ Proving...
% 39.86/5.48  ------ Problem Properties 
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  clauses                                 14
% 39.86/5.48  conjectures                             2
% 39.86/5.48  EPR                                     2
% 39.86/5.48  Horn                                    14
% 39.86/5.48  unary                                   10
% 39.86/5.48  binary                                  3
% 39.86/5.48  lits                                    19
% 39.86/5.48  lits eq                                 10
% 39.86/5.48  fd_pure                                 0
% 39.86/5.48  fd_pseudo                               0
% 39.86/5.48  fd_cond                                 0
% 39.86/5.48  fd_pseudo_cond                          0
% 39.86/5.48  AC symbols                              0
% 39.86/5.48  
% 39.86/5.48  ------ Input Options Time Limit: Unbounded
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 39.86/5.48  Current options:
% 39.86/5.48  ------ 
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.86/5.48  
% 39.86/5.48  ------ Proving...
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  % SZS status Theorem for theBenchmark.p
% 39.86/5.48  
% 39.86/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.86/5.48  
% 39.86/5.48  fof(f14,conjecture,(
% 39.86/5.48    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f15,negated_conjecture,(
% 39.86/5.48    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 39.86/5.48    inference(negated_conjecture,[],[f14])).
% 39.86/5.48  
% 39.86/5.48  fof(f19,plain,(
% 39.86/5.48    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 39.86/5.48    inference(ennf_transformation,[],[f15])).
% 39.86/5.48  
% 39.86/5.48  fof(f21,plain,(
% 39.86/5.48    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 39.86/5.48    introduced(choice_axiom,[])).
% 39.86/5.48  
% 39.86/5.48  fof(f22,plain,(
% 39.86/5.48    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 39.86/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21])).
% 39.86/5.48  
% 39.86/5.48  fof(f37,plain,(
% 39.86/5.48    r1_tarski(sK2,sK1)),
% 39.86/5.48    inference(cnf_transformation,[],[f22])).
% 39.86/5.48  
% 39.86/5.48  fof(f7,axiom,(
% 39.86/5.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f18,plain,(
% 39.86/5.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.86/5.48    inference(ennf_transformation,[],[f7])).
% 39.86/5.48  
% 39.86/5.48  fof(f30,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.86/5.48    inference(cnf_transformation,[],[f18])).
% 39.86/5.48  
% 39.86/5.48  fof(f9,axiom,(
% 39.86/5.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f32,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.86/5.48    inference(cnf_transformation,[],[f9])).
% 39.86/5.48  
% 39.86/5.48  fof(f43,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 39.86/5.48    inference(definition_unfolding,[],[f30,f32])).
% 39.86/5.48  
% 39.86/5.48  fof(f1,axiom,(
% 39.86/5.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f23,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.86/5.48    inference(cnf_transformation,[],[f1])).
% 39.86/5.48  
% 39.86/5.48  fof(f40,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 39.86/5.48    inference(definition_unfolding,[],[f23,f32,f32])).
% 39.86/5.48  
% 39.86/5.48  fof(f10,axiom,(
% 39.86/5.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f33,plain,(
% 39.86/5.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 39.86/5.48    inference(cnf_transformation,[],[f10])).
% 39.86/5.48  
% 39.86/5.48  fof(f44,plain,(
% 39.86/5.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 39.86/5.48    inference(definition_unfolding,[],[f33,f32,f32])).
% 39.86/5.48  
% 39.86/5.48  fof(f3,axiom,(
% 39.86/5.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f26,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.86/5.48    inference(cnf_transformation,[],[f3])).
% 39.86/5.48  
% 39.86/5.48  fof(f39,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 39.86/5.48    inference(definition_unfolding,[],[f26,f32])).
% 39.86/5.48  
% 39.86/5.48  fof(f12,axiom,(
% 39.86/5.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f35,plain,(
% 39.86/5.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 39.86/5.48    inference(cnf_transformation,[],[f12])).
% 39.86/5.48  
% 39.86/5.48  fof(f38,plain,(
% 39.86/5.48    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 39.86/5.48    inference(cnf_transformation,[],[f22])).
% 39.86/5.48  
% 39.86/5.48  fof(f13,axiom,(
% 39.86/5.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 39.86/5.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.86/5.48  
% 39.86/5.48  fof(f36,plain,(
% 39.86/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 39.86/5.48    inference(cnf_transformation,[],[f13])).
% 39.86/5.48  
% 39.86/5.48  fof(f45,plain,(
% 39.86/5.48    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 39.86/5.48    inference(definition_unfolding,[],[f38,f36,f32])).
% 39.86/5.48  
% 39.86/5.48  cnf(c_13,negated_conjecture,
% 39.86/5.48      ( r1_tarski(sK2,sK1) ),
% 39.86/5.48      inference(cnf_transformation,[],[f37]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_147230,plain,
% 39.86/5.48      ( r1_tarski(sK2,sK1) = iProver_top ),
% 39.86/5.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_7,plain,
% 39.86/5.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 39.86/5.48      inference(cnf_transformation,[],[f43]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_147232,plain,
% 39.86/5.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 39.86/5.48      | r1_tarski(X0,X1) != iProver_top ),
% 39.86/5.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_147357,plain,
% 39.86/5.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_147230,c_147232]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_1,plain,
% 39.86/5.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 39.86/5.48      inference(cnf_transformation,[],[f40]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_9,plain,
% 39.86/5.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 39.86/5.48      inference(cnf_transformation,[],[f44]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_147376,plain,
% 39.86/5.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_150068,plain,
% 39.86/5.48      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_147357,c_147376]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_0,plain,
% 39.86/5.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 39.86/5.48      inference(cnf_transformation,[],[f39]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_147301,plain,
% 39.86/5.48      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_147393,plain,
% 39.86/5.48      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_9,c_147301]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_147398,plain,
% 39.86/5.48      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 39.86/5.48      inference(demodulation,[status(thm)],[c_147393,c_9]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_166144,plain,
% 39.86/5.48      ( k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_150068,c_147398]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_166530,plain,
% 39.86/5.48      ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,sK2) ),
% 39.86/5.48      inference(demodulation,[status(thm)],[c_166144,c_147301,c_150068]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_166674,plain,
% 39.86/5.48      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
% 39.86/5.48      inference(instantiation,[status(thm)],[c_166530]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_7413,plain,
% 39.86/5.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_7296,plain,
% 39.86/5.48      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_9066,plain,
% 39.86/5.48      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_7413,c_7296]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_9316,plain,
% 39.86/5.48      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 39.86/5.48      inference(demodulation,[status(thm)],[c_9066,c_9]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_11,plain,
% 39.86/5.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 39.86/5.48      inference(cnf_transformation,[],[f35]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_7304,plain,
% 39.86/5.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_13282,plain,
% 39.86/5.48      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 39.86/5.48      inference(superposition,[status(thm)],[c_9316,c_7304]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_13300,plain,
% 39.86/5.48      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 39.86/5.48      inference(light_normalisation,[status(thm)],[c_13282,c_9]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_13301,plain,
% 39.86/5.48      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 39.86/5.48      inference(demodulation,[status(thm)],[c_13300,c_0]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_12,negated_conjecture,
% 39.86/5.48      ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
% 39.86/5.48      inference(cnf_transformation,[],[f45]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_7266,plain,
% 39.86/5.48      ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) != k4_xboole_0(sK0,sK2) ),
% 39.86/5.48      inference(demodulation,[status(thm)],[c_12,c_9]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(c_145526,plain,
% 39.86/5.48      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
% 39.86/5.48      inference(demodulation,[status(thm)],[c_13301,c_7266]) ).
% 39.86/5.48  
% 39.86/5.48  cnf(contradiction,plain,
% 39.86/5.48      ( $false ),
% 39.86/5.48      inference(minisat,[status(thm)],[c_166674,c_145526]) ).
% 39.86/5.48  
% 39.86/5.48  
% 39.86/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.86/5.48  
% 39.86/5.48  ------                               Statistics
% 39.86/5.48  
% 39.86/5.48  ------ Selected
% 39.86/5.48  
% 39.86/5.48  total_time:                             4.818
% 39.86/5.48  
%------------------------------------------------------------------------------
