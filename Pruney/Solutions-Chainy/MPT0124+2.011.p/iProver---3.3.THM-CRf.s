%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:13 EST 2020

% Result     : Theorem 43.27s
% Output     : CNFRefutation 43.27s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).

fof(f36,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f31,f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f37,f35,f31])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_147233,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_147235,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_147359,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_147233,c_147235])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_147378,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_150156,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_147359,c_147378])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_147297,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_147395,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_9,c_147297])).

cnf(c_147400,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_147395,c_9])).

cnf(c_167094,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_150156,c_147400])).

cnf(c_167472,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,sK2) ),
    inference(demodulation,[status(thm)],[c_167094,c_147297,c_150156])).

cnf(c_167604,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_167472])).

cnf(c_7415,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_7298,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_9068,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7415,c_7298])).

cnf(c_9318,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_9068,c_9])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7306,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_13284,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_9318,c_7306])).

cnf(c_13302,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_13284,c_9])).

cnf(c_13303,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_13302,c_0])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7268,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) != k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_12,c_9])).

cnf(c_145528,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_13303,c_7268])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_167604,c_145528])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:03:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 43.27/5.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.27/5.99  
% 43.27/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.27/5.99  
% 43.27/5.99  ------  iProver source info
% 43.27/5.99  
% 43.27/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.27/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.27/5.99  git: non_committed_changes: false
% 43.27/5.99  git: last_make_outside_of_git: false
% 43.27/5.99  
% 43.27/5.99  ------ 
% 43.27/5.99  ------ Parsing...
% 43.27/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  ------ Proving...
% 43.27/5.99  ------ Problem Properties 
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  clauses                                 14
% 43.27/5.99  conjectures                             2
% 43.27/5.99  EPR                                     1
% 43.27/5.99  Horn                                    14
% 43.27/5.99  unary                                   10
% 43.27/5.99  binary                                  4
% 43.27/5.99  lits                                    18
% 43.27/5.99  lits eq                                 10
% 43.27/5.99  fd_pure                                 0
% 43.27/5.99  fd_pseudo                               0
% 43.27/5.99  fd_cond                                 0
% 43.27/5.99  fd_pseudo_cond                          0
% 43.27/5.99  AC symbols                              0
% 43.27/5.99  
% 43.27/5.99  ------ Input Options Time Limit: Unbounded
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 43.27/5.99  Current options:
% 43.27/5.99  ------ 
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/5.99  
% 43.27/5.99  ------ Proving...
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  % SZS status Theorem for theBenchmark.p
% 43.27/5.99  
% 43.27/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.27/5.99  
% 43.27/5.99  fof(f14,conjecture,(
% 43.27/5.99    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f15,negated_conjecture,(
% 43.27/5.99    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 43.27/5.99    inference(negated_conjecture,[],[f14])).
% 43.27/5.99  
% 43.27/5.99  fof(f18,plain,(
% 43.27/5.99    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 43.27/5.99    inference(ennf_transformation,[],[f15])).
% 43.27/5.99  
% 43.27/5.99  fof(f20,plain,(
% 43.27/5.99    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 43.27/5.99    introduced(choice_axiom,[])).
% 43.27/5.99  
% 43.27/5.99  fof(f21,plain,(
% 43.27/5.99    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 43.27/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).
% 43.27/5.99  
% 43.27/5.99  fof(f36,plain,(
% 43.27/5.99    r1_tarski(sK2,sK1)),
% 43.27/5.99    inference(cnf_transformation,[],[f21])).
% 43.27/5.99  
% 43.27/5.99  fof(f7,axiom,(
% 43.27/5.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f17,plain,(
% 43.27/5.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 43.27/5.99    inference(ennf_transformation,[],[f7])).
% 43.27/5.99  
% 43.27/5.99  fof(f29,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 43.27/5.99    inference(cnf_transformation,[],[f17])).
% 43.27/5.99  
% 43.27/5.99  fof(f9,axiom,(
% 43.27/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f31,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.27/5.99    inference(cnf_transformation,[],[f9])).
% 43.27/5.99  
% 43.27/5.99  fof(f43,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 43.27/5.99    inference(definition_unfolding,[],[f29,f31])).
% 43.27/5.99  
% 43.27/5.99  fof(f1,axiom,(
% 43.27/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f22,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.27/5.99    inference(cnf_transformation,[],[f1])).
% 43.27/5.99  
% 43.27/5.99  fof(f39,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 43.27/5.99    inference(definition_unfolding,[],[f22,f31,f31])).
% 43.27/5.99  
% 43.27/5.99  fof(f10,axiom,(
% 43.27/5.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f32,plain,(
% 43.27/5.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 43.27/5.99    inference(cnf_transformation,[],[f10])).
% 43.27/5.99  
% 43.27/5.99  fof(f44,plain,(
% 43.27/5.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 43.27/5.99    inference(definition_unfolding,[],[f32,f31,f31])).
% 43.27/5.99  
% 43.27/5.99  fof(f3,axiom,(
% 43.27/5.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f25,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.27/5.99    inference(cnf_transformation,[],[f3])).
% 43.27/5.99  
% 43.27/5.99  fof(f38,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 43.27/5.99    inference(definition_unfolding,[],[f25,f31])).
% 43.27/5.99  
% 43.27/5.99  fof(f12,axiom,(
% 43.27/5.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f34,plain,(
% 43.27/5.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 43.27/5.99    inference(cnf_transformation,[],[f12])).
% 43.27/5.99  
% 43.27/5.99  fof(f37,plain,(
% 43.27/5.99    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 43.27/5.99    inference(cnf_transformation,[],[f21])).
% 43.27/5.99  
% 43.27/5.99  fof(f13,axiom,(
% 43.27/5.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 43.27/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/5.99  
% 43.27/5.99  fof(f35,plain,(
% 43.27/5.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 43.27/5.99    inference(cnf_transformation,[],[f13])).
% 43.27/5.99  
% 43.27/5.99  fof(f45,plain,(
% 43.27/5.99    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 43.27/5.99    inference(definition_unfolding,[],[f37,f35,f31])).
% 43.27/5.99  
% 43.27/5.99  cnf(c_13,negated_conjecture,
% 43.27/5.99      ( r1_tarski(sK2,sK1) ),
% 43.27/5.99      inference(cnf_transformation,[],[f36]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_147233,plain,
% 43.27/5.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 43.27/5.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_7,plain,
% 43.27/5.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.27/5.99      inference(cnf_transformation,[],[f43]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_147235,plain,
% 43.27/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 43.27/5.99      | r1_tarski(X0,X1) != iProver_top ),
% 43.27/5.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_147359,plain,
% 43.27/5.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_147233,c_147235]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_1,plain,
% 43.27/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.27/5.99      inference(cnf_transformation,[],[f39]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_9,plain,
% 43.27/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 43.27/5.99      inference(cnf_transformation,[],[f44]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_147378,plain,
% 43.27/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_150156,plain,
% 43.27/5.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_147359,c_147378]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_0,plain,
% 43.27/5.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.27/5.99      inference(cnf_transformation,[],[f38]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_147297,plain,
% 43.27/5.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_147395,plain,
% 43.27/5.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_9,c_147297]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_147400,plain,
% 43.27/5.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.27/5.99      inference(demodulation,[status(thm)],[c_147395,c_9]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_167094,plain,
% 43.27/5.99      ( k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_150156,c_147400]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_167472,plain,
% 43.27/5.99      ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,sK2) ),
% 43.27/5.99      inference(demodulation,[status(thm)],[c_167094,c_147297,c_150156]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_167604,plain,
% 43.27/5.99      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
% 43.27/5.99      inference(instantiation,[status(thm)],[c_167472]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_7415,plain,
% 43.27/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_7298,plain,
% 43.27/5.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_9068,plain,
% 43.27/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_7415,c_7298]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_9318,plain,
% 43.27/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/5.99      inference(demodulation,[status(thm)],[c_9068,c_9]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_11,plain,
% 43.27/5.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.27/5.99      inference(cnf_transformation,[],[f34]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_7306,plain,
% 43.27/5.99      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_13284,plain,
% 43.27/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 43.27/5.99      inference(superposition,[status(thm)],[c_9318,c_7306]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_13302,plain,
% 43.27/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 43.27/5.99      inference(light_normalisation,[status(thm)],[c_13284,c_9]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_13303,plain,
% 43.27/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.27/5.99      inference(demodulation,[status(thm)],[c_13302,c_0]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_12,negated_conjecture,
% 43.27/5.99      ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
% 43.27/5.99      inference(cnf_transformation,[],[f45]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_7268,plain,
% 43.27/5.99      ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) != k4_xboole_0(sK0,sK2) ),
% 43.27/5.99      inference(demodulation,[status(thm)],[c_12,c_9]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(c_145528,plain,
% 43.27/5.99      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
% 43.27/5.99      inference(demodulation,[status(thm)],[c_13303,c_7268]) ).
% 43.27/5.99  
% 43.27/5.99  cnf(contradiction,plain,
% 43.27/5.99      ( $false ),
% 43.27/5.99      inference(minisat,[status(thm)],[c_167604,c_145528]) ).
% 43.27/5.99  
% 43.27/5.99  
% 43.27/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.27/5.99  
% 43.27/5.99  ------                               Statistics
% 43.27/5.99  
% 43.27/5.99  ------ Selected
% 43.27/5.99  
% 43.27/5.99  total_time:                             5.152
% 43.27/5.99  
%------------------------------------------------------------------------------
