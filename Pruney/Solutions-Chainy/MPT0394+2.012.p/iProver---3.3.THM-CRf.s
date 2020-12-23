%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:40 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 170 expanded)
%              Number of clauses        :   23 (  48 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 270 expanded)
%              Number of equality atoms :   74 ( 199 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f32])).

fof(f56,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f56,f49,f51])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1) ) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f44,f49])).

cnf(c_19,plain,
    ( k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,plain,
    ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8329,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1))
    | k1_tarski(X0) = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_19,c_18])).

cnf(c_12820,plain,
    ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | k1_tarski(X0) = k1_xboole_0
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19,c_8329])).

cnf(c_20,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19316,plain,
    ( k1_tarski(sK3) = k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12820,c_20])).

cnf(c_21308,plain,
    ( k1_setfam_1(k1_xboole_0) = sK3
    | k1_tarski(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19316,c_19])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_43,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_45,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_47,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8120,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1)
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9299,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_8120])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8121,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8205,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_8121])).

cnf(c_10313,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9299,c_8205])).

cnf(c_21303,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19316,c_10313])).

cnf(c_21341,plain,
    ( k1_tarski(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21308,c_43,c_47,c_21303])).

cnf(c_21355,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21341,c_10313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21355,c_47,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.20/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.20/1.53  
% 7.20/1.53  ------  iProver source info
% 7.20/1.53  
% 7.20/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.20/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.20/1.53  git: non_committed_changes: false
% 7.20/1.53  git: last_make_outside_of_git: false
% 7.20/1.53  
% 7.20/1.53  ------ 
% 7.20/1.53  ------ Parsing...
% 7.20/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  ------ Proving...
% 7.20/1.53  ------ Problem Properties 
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  clauses                                 20
% 7.20/1.53  conjectures                             2
% 7.20/1.53  EPR                                     2
% 7.20/1.53  Horn                                    16
% 7.20/1.53  unary                                   7
% 7.20/1.53  binary                                  7
% 7.20/1.53  lits                                    40
% 7.20/1.53  lits eq                                 15
% 7.20/1.53  fd_pure                                 0
% 7.20/1.53  fd_pseudo                               0
% 7.20/1.53  fd_cond                                 1
% 7.20/1.53  fd_pseudo_cond                          4
% 7.20/1.53  AC symbols                              0
% 7.20/1.53  
% 7.20/1.53  ------ Input Options Time Limit: Unbounded
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.20/1.53  Current options:
% 7.20/1.53  ------ 
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  % SZS status Theorem for theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  fof(f13,axiom,(
% 7.20/1.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f55,plain,(
% 7.20/1.53    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 7.20/1.53    inference(cnf_transformation,[],[f13])).
% 7.20/1.53  
% 7.20/1.53  fof(f12,axiom,(
% 7.20/1.53    ! [X0,X1] : ~(k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f20,plain,(
% 7.20/1.53    ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.20/1.53    inference(ennf_transformation,[],[f12])).
% 7.20/1.53  
% 7.20/1.53  fof(f54,plain,(
% 7.20/1.53    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.20/1.53    inference(cnf_transformation,[],[f20])).
% 7.20/1.53  
% 7.20/1.53  fof(f7,axiom,(
% 7.20/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f49,plain,(
% 7.20/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.20/1.53    inference(cnf_transformation,[],[f7])).
% 7.20/1.53  
% 7.20/1.53  fof(f72,plain,(
% 7.20/1.53    ( ! [X0,X1] : (k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.20/1.53    inference(definition_unfolding,[],[f54,f49])).
% 7.20/1.53  
% 7.20/1.53  fof(f14,conjecture,(
% 7.20/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f15,negated_conjecture,(
% 7.20/1.53    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.20/1.53    inference(negated_conjecture,[],[f14])).
% 7.20/1.53  
% 7.20/1.53  fof(f21,plain,(
% 7.20/1.53    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 7.20/1.53    inference(ennf_transformation,[],[f15])).
% 7.20/1.53  
% 7.20/1.53  fof(f32,plain,(
% 7.20/1.53    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f33,plain,(
% 7.20/1.53    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 7.20/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f32])).
% 7.20/1.53  
% 7.20/1.53  fof(f56,plain,(
% 7.20/1.53    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 7.20/1.53    inference(cnf_transformation,[],[f33])).
% 7.20/1.53  
% 7.20/1.53  fof(f9,axiom,(
% 7.20/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f51,plain,(
% 7.20/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 7.20/1.53    inference(cnf_transformation,[],[f9])).
% 7.20/1.53  
% 7.20/1.53  fof(f73,plain,(
% 7.20/1.53    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),
% 7.20/1.53    inference(definition_unfolding,[],[f56,f49,f51])).
% 7.20/1.53  
% 7.20/1.53  fof(f3,axiom,(
% 7.20/1.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f16,plain,(
% 7.20/1.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.20/1.53    inference(rectify,[],[f3])).
% 7.20/1.53  
% 7.20/1.53  fof(f42,plain,(
% 7.20/1.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.20/1.53    inference(cnf_transformation,[],[f16])).
% 7.20/1.53  
% 7.20/1.53  fof(f66,plain,(
% 7.20/1.53    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.20/1.53    inference(definition_unfolding,[],[f42,f49])).
% 7.20/1.53  
% 7.20/1.53  fof(f2,axiom,(
% 7.20/1.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f27,plain,(
% 7.20/1.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.20/1.53    inference(nnf_transformation,[],[f2])).
% 7.20/1.53  
% 7.20/1.53  fof(f41,plain,(
% 7.20/1.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.20/1.53    inference(cnf_transformation,[],[f27])).
% 7.20/1.53  
% 7.20/1.53  fof(f64,plain,(
% 7.20/1.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.20/1.53    inference(definition_unfolding,[],[f41,f49])).
% 7.20/1.53  
% 7.20/1.53  fof(f11,axiom,(
% 7.20/1.53    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f19,plain,(
% 7.20/1.53    ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1))),
% 7.20/1.53    inference(ennf_transformation,[],[f11])).
% 7.20/1.53  
% 7.20/1.53  fof(f53,plain,(
% 7.20/1.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f19])).
% 7.20/1.53  
% 7.20/1.53  fof(f71,plain,(
% 7.20/1.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1)) )),
% 7.20/1.53    inference(definition_unfolding,[],[f53,f49])).
% 7.20/1.53  
% 7.20/1.53  fof(f4,axiom,(
% 7.20/1.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f17,plain,(
% 7.20/1.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.20/1.53    inference(rectify,[],[f4])).
% 7.20/1.53  
% 7.20/1.53  fof(f18,plain,(
% 7.20/1.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.20/1.53    inference(ennf_transformation,[],[f17])).
% 7.20/1.53  
% 7.20/1.53  fof(f28,plain,(
% 7.20/1.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f29,plain,(
% 7.20/1.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.20/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f28])).
% 7.20/1.53  
% 7.20/1.53  fof(f44,plain,(
% 7.20/1.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.20/1.53    inference(cnf_transformation,[],[f29])).
% 7.20/1.53  
% 7.20/1.53  fof(f67,plain,(
% 7.20/1.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.20/1.53    inference(definition_unfolding,[],[f44,f49])).
% 7.20/1.53  
% 7.20/1.53  cnf(c_19,plain,
% 7.20/1.53      ( k1_setfam_1(k1_tarski(X0)) = X0 ),
% 7.20/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_18,plain,
% 7.20/1.53      ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1))
% 7.20/1.53      | k1_xboole_0 = X1
% 7.20/1.53      | k1_xboole_0 = X0 ),
% 7.20/1.53      inference(cnf_transformation,[],[f72]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_8329,plain,
% 7.20/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1))
% 7.20/1.53      | k1_tarski(X0) = k1_xboole_0
% 7.20/1.53      | k1_xboole_0 = X1 ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_19,c_18]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_12820,plain,
% 7.20/1.53      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 7.20/1.53      | k1_tarski(X0) = k1_xboole_0
% 7.20/1.53      | k1_tarski(X1) = k1_xboole_0 ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_19,c_8329]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_20,negated_conjecture,
% 7.20/1.53      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
% 7.20/1.53      inference(cnf_transformation,[],[f73]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_19316,plain,
% 7.20/1.53      ( k1_tarski(sK3) = k1_xboole_0 | k1_tarski(sK2) = k1_xboole_0 ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_12820,c_20]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_21308,plain,
% 7.20/1.53      ( k1_setfam_1(k1_xboole_0) = sK3 | k1_tarski(sK2) = k1_xboole_0 ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_19316,c_19]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_9,plain,
% 7.20/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.20/1.53      inference(cnf_transformation,[],[f66]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_43,plain,
% 7.20/1.53      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_7,plain,
% 7.20/1.53      ( r1_xboole_0(X0,X1)
% 7.20/1.53      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.20/1.53      inference(cnf_transformation,[],[f64]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_45,plain,
% 7.20/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.20/1.53      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_47,plain,
% 7.20/1.53      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 7.20/1.53      | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_45]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_17,plain,
% 7.20/1.53      ( r2_hidden(X0,X1)
% 7.20/1.53      | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
% 7.20/1.53      inference(cnf_transformation,[],[f71]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_8120,plain,
% 7.20/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1)
% 7.20/1.53      | r2_hidden(X1,X0) = iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_9299,plain,
% 7.20/1.53      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_9,c_8120]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_10,negated_conjecture,
% 7.20/1.53      ( ~ r1_xboole_0(X0,X1)
% 7.20/1.53      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.20/1.53      inference(cnf_transformation,[],[f67]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_8121,plain,
% 7.20/1.53      ( r1_xboole_0(X0,X1) != iProver_top
% 7.20/1.53      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_8205,plain,
% 7.20/1.53      ( r1_xboole_0(X0,X0) != iProver_top
% 7.20/1.53      | r2_hidden(X1,X0) != iProver_top ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_9,c_8121]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_10313,plain,
% 7.20/1.53      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) != iProver_top ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_9299,c_8205]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_21303,plain,
% 7.20/1.53      ( k1_tarski(sK2) = k1_xboole_0
% 7.20/1.53      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_19316,c_10313]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_21341,plain,
% 7.20/1.53      ( k1_tarski(sK2) = k1_xboole_0 ),
% 7.20/1.53      inference(global_propositional_subsumption,
% 7.20/1.53                [status(thm)],
% 7.20/1.53                [c_21308,c_43,c_47,c_21303]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_21355,plain,
% 7.20/1.53      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_21341,c_10313]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(contradiction,plain,
% 7.20/1.53      ( $false ),
% 7.20/1.53      inference(minisat,[status(thm)],[c_21355,c_47,c_43]) ).
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  ------                               Statistics
% 7.20/1.53  
% 7.20/1.53  ------ Selected
% 7.20/1.53  
% 7.20/1.53  total_time:                             0.502
% 7.20/1.53  
%------------------------------------------------------------------------------
