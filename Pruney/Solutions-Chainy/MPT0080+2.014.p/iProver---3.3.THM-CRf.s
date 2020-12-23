%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:55 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 176 expanded)
%              Number of clauses        :   44 (  73 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  107 ( 234 expanded)
%              Number of equality atoms :   66 ( 151 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK2,sK3)
      & r1_xboole_0(sK2,sK4)
      & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(sK2,sK3)
    & r1_xboole_0(sK2,sK4)
    & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f30])).

fof(f51,plain,(
    r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2437,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2443,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7775,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2437,c_2443])).

cnf(c_14,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8219,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_7775,c_14])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2734,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_8450,plain,
    ( k4_xboole_0(sK2,sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_8219,c_2734])).

cnf(c_13,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8775,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_8450,c_13])).

cnf(c_12,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2868,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_10])).

cnf(c_2873,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2868,c_10])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2436,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2441,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4856,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2436,c_2441])).

cnf(c_5051,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4856,c_12])).

cnf(c_2867,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2734,c_12])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3006,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_14])).

cnf(c_3363,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_2867,c_3006])).

cnf(c_3643,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3363,c_14])).

cnf(c_3850,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3643,c_2867])).

cnf(c_5063,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5051,c_3850])).

cnf(c_5223,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_5063,c_13])).

cnf(c_5228,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5223,c_3643])).

cnf(c_5439,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK3,sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_5228])).

cnf(c_5694,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2873,c_5439])).

cnf(c_10044,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8775,c_5694])).

cnf(c_10746,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10044,c_10])).

cnf(c_10754,plain,
    ( k2_xboole_0(sK3,sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_10746,c_9])).

cnf(c_16,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2439,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3108,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2439])).

cnf(c_11554,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10754,c_3108])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11554,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:30:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.89/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/1.03  
% 3.89/1.03  ------  iProver source info
% 3.89/1.03  
% 3.89/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.89/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/1.03  git: non_committed_changes: false
% 3.89/1.03  git: last_make_outside_of_git: false
% 3.89/1.03  
% 3.89/1.03  ------ 
% 3.89/1.03  ------ Parsing...
% 3.89/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  ------ Proving...
% 3.89/1.03  ------ Problem Properties 
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  clauses                                 20
% 3.89/1.03  conjectures                             3
% 3.89/1.03  EPR                                     4
% 3.89/1.03  Horn                                    18
% 3.89/1.03  unary                                   12
% 3.89/1.03  binary                                  7
% 3.89/1.03  lits                                    29
% 3.89/1.03  lits eq                                 10
% 3.89/1.03  fd_pure                                 0
% 3.89/1.03  fd_pseudo                               0
% 3.89/1.03  fd_cond                                 0
% 3.89/1.03  fd_pseudo_cond                          0
% 3.89/1.03  AC symbols                              0
% 3.89/1.03  
% 3.89/1.03  ------ Input Options Time Limit: Unbounded
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing...
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.89/1.03  Current options:
% 3.89/1.03  ------ 
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  % SZS status Theorem for theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  fof(f15,conjecture,(
% 3.89/1.03    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f16,negated_conjecture,(
% 3.89/1.03    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.89/1.03    inference(negated_conjecture,[],[f15])).
% 3.89/1.03  
% 3.89/1.03  fof(f21,plain,(
% 3.89/1.03    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.89/1.03    inference(ennf_transformation,[],[f16])).
% 3.89/1.03  
% 3.89/1.03  fof(f22,plain,(
% 3.89/1.03    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.89/1.03    inference(flattening,[],[f21])).
% 3.89/1.03  
% 3.89/1.03  fof(f30,plain,(
% 3.89/1.03    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4)))),
% 3.89/1.03    introduced(choice_axiom,[])).
% 3.89/1.03  
% 3.89/1.03  fof(f31,plain,(
% 3.89/1.03    ~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 3.89/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f30])).
% 3.89/1.03  
% 3.89/1.03  fof(f51,plain,(
% 3.89/1.03    r1_xboole_0(sK2,sK4)),
% 3.89/1.03    inference(cnf_transformation,[],[f31])).
% 3.89/1.03  
% 3.89/1.03  fof(f3,axiom,(
% 3.89/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f27,plain,(
% 3.89/1.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.89/1.03    inference(nnf_transformation,[],[f3])).
% 3.89/1.03  
% 3.89/1.03  fof(f36,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f27])).
% 3.89/1.03  
% 3.89/1.03  fof(f11,axiom,(
% 3.89/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f46,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f11])).
% 3.89/1.03  
% 3.89/1.03  fof(f54,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.89/1.03    inference(definition_unfolding,[],[f36,f46])).
% 3.89/1.03  
% 3.89/1.03  fof(f12,axiom,(
% 3.89/1.03    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f47,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.89/1.03    inference(cnf_transformation,[],[f12])).
% 3.89/1.03  
% 3.89/1.03  fof(f57,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.89/1.03    inference(definition_unfolding,[],[f47,f46])).
% 3.89/1.03  
% 3.89/1.03  fof(f6,axiom,(
% 3.89/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f41,plain,(
% 3.89/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.89/1.03    inference(cnf_transformation,[],[f6])).
% 3.89/1.03  
% 3.89/1.03  fof(f1,axiom,(
% 3.89/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f32,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f1])).
% 3.89/1.03  
% 3.89/1.03  fof(f10,axiom,(
% 3.89/1.03    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f45,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f10])).
% 3.89/1.03  
% 3.89/1.03  fof(f9,axiom,(
% 3.89/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f44,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f9])).
% 3.89/1.03  
% 3.89/1.03  fof(f7,axiom,(
% 3.89/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f42,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f7])).
% 3.89/1.03  
% 3.89/1.03  fof(f50,plain,(
% 3.89/1.03    r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 3.89/1.03    inference(cnf_transformation,[],[f31])).
% 3.89/1.03  
% 3.89/1.03  fof(f5,axiom,(
% 3.89/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f20,plain,(
% 3.89/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.89/1.03    inference(ennf_transformation,[],[f5])).
% 3.89/1.03  
% 3.89/1.03  fof(f40,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f20])).
% 3.89/1.03  
% 3.89/1.03  fof(f8,axiom,(
% 3.89/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f43,plain,(
% 3.89/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.89/1.03    inference(cnf_transformation,[],[f8])).
% 3.89/1.03  
% 3.89/1.03  fof(f14,axiom,(
% 3.89/1.03    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f49,plain,(
% 3.89/1.03    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f14])).
% 3.89/1.03  
% 3.89/1.03  fof(f52,plain,(
% 3.89/1.03    ~r1_tarski(sK2,sK3)),
% 3.89/1.03    inference(cnf_transformation,[],[f31])).
% 3.89/1.03  
% 3.89/1.03  cnf(c_18,negated_conjecture,
% 3.89/1.03      ( r1_xboole_0(sK2,sK4) ),
% 3.89/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2437,plain,
% 3.89/1.03      ( r1_xboole_0(sK2,sK4) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5,plain,
% 3.89/1.03      ( ~ r1_xboole_0(X0,X1)
% 3.89/1.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.89/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2443,plain,
% 3.89/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.89/1.03      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_7775,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_2437,c_2443]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_14,plain,
% 3.89/1.03      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.89/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8219,plain,
% 3.89/1.03      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK4)) = sK2 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_7775,c_14]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9,plain,
% 3.89/1.03      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.89/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_0,plain,
% 3.89/1.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2734,plain,
% 3.89/1.03      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8450,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,sK4) = sK2 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_8219,c_2734]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_13,plain,
% 3.89/1.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.89/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8775,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK2,X0) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_8450,c_13]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_12,plain,
% 3.89/1.03      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.89/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_10,plain,
% 3.89/1.03      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.89/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2868,plain,
% 3.89/1.03      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_12,c_10]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2873,plain,
% 3.89/1.03      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.89/1.03      inference(light_normalisation,[status(thm)],[c_2868,c_10]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_19,negated_conjecture,
% 3.89/1.03      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.89/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2436,plain,
% 3.89/1.03      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8,plain,
% 3.89/1.03      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.89/1.03      inference(cnf_transformation,[],[f40]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2441,plain,
% 3.89/1.03      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_4856,plain,
% 3.89/1.03      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k2_xboole_0(sK3,sK4) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_2436,c_2441]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5051,plain,
% 3.89/1.03      ( k4_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_4856,c_12]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2867,plain,
% 3.89/1.03      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_2734,c_12]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11,plain,
% 3.89/1.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.89/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3006,plain,
% 3.89/1.03      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_11,c_14]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3363,plain,
% 3.89/1.03      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_2867,c_3006]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3643,plain,
% 3.89/1.03      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_3363,c_14]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3850,plain,
% 3.89/1.03      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.89/1.03      inference(demodulation,[status(thm)],[c_3643,c_2867]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5063,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k1_xboole_0 ),
% 3.89/1.03      inference(demodulation,[status(thm)],[c_5051,c_3850]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5223,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_5063,c_13]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5228,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),X0)) = k1_xboole_0 ),
% 3.89/1.03      inference(light_normalisation,[status(thm)],[c_5223,c_3643]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5439,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK3,sK4))) = k1_xboole_0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_0,c_5228]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5694,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) = k1_xboole_0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_2873,c_5439]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_10044,plain,
% 3.89/1.03      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_8775,c_5694]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_10746,plain,
% 3.89/1.03      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k1_xboole_0) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_10044,c_10]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_10754,plain,
% 3.89/1.03      ( k2_xboole_0(sK3,sK2) = sK3 ),
% 3.89/1.03      inference(demodulation,[status(thm)],[c_10746,c_9]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_16,plain,
% 3.89/1.03      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.89/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2439,plain,
% 3.89/1.03      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3108,plain,
% 3.89/1.03      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_0,c_2439]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11554,plain,
% 3.89/1.03      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_10754,c_3108]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_17,negated_conjecture,
% 3.89/1.03      ( ~ r1_tarski(sK2,sK3) ),
% 3.89/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_22,plain,
% 3.89/1.03      ( r1_tarski(sK2,sK3) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(contradiction,plain,
% 3.89/1.03      ( $false ),
% 3.89/1.03      inference(minisat,[status(thm)],[c_11554,c_22]) ).
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  ------                               Statistics
% 3.89/1.03  
% 3.89/1.03  ------ Selected
% 3.89/1.03  
% 3.89/1.03  total_time:                             0.376
% 3.89/1.03  
%------------------------------------------------------------------------------
