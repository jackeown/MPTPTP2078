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
% DateTime   : Thu Dec  3 11:25:48 EST 2020

% Result     : Theorem 35.55s
% Output     : CNFRefutation 35.55s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 171 expanded)
%              Number of clauses        :   48 (  74 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 ( 285 expanded)
%              Number of equality atoms :   84 ( 155 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f31,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f31,f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_375,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_380,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1910,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_375,c_380])).

cnf(c_155288,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1910,c_0])).

cnf(c_156726,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_155288])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_124,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(theory_normalisation,[status(thm)],[c_12,c_5,c_0])).

cnf(c_373,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_377,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1777,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_373,c_377])).

cnf(c_429,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_2293,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_1777,c_429])).

cnf(c_159247,plain,
    ( k3_xboole_0(sK2,sK0) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_156726,c_2293])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_159444,plain,
    ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_159247,c_7])).

cnf(c_8,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_376,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_954,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_376])).

cnf(c_1778,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_954,c_377])).

cnf(c_2283,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1777,c_5])).

cnf(c_115198,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1778,c_2283])).

cnf(c_116155,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_115198,c_1777])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_378,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_118373,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_116155,c_378])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_118746,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_118373,c_10])).

cnf(c_118747,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_118746])).

cnf(c_127,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_722,plain,
    ( X0 != X1
    | X0 = k3_xboole_0(X2,X3)
    | k3_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_1459,plain,
    ( k3_xboole_0(sK2,sK0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1460,plain,
    ( k3_xboole_0(sK2,sK0) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_591,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_519,plain,
    ( k3_xboole_0(sK0,sK2) != X0
    | k3_xboole_0(sK0,sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_590,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK2,sK0)
    | k3_xboole_0(sK0,sK2) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_456,plain,
    ( r1_xboole_0(sK0,sK2)
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_457,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_126,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_136,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,plain,
    ( r1_tarski(sK0,sK1) != iProver_top
    | r1_xboole_0(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_159444,c_118747,c_1460,c_591,c_590,c_457,c_136,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.55/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.55/5.00  
% 35.55/5.00  ------  iProver source info
% 35.55/5.00  
% 35.55/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.55/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.55/5.00  git: non_committed_changes: false
% 35.55/5.00  git: last_make_outside_of_git: false
% 35.55/5.00  
% 35.55/5.00  ------ 
% 35.55/5.00  ------ Parsing...
% 35.55/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.55/5.00  ------ Proving...
% 35.55/5.00  ------ Problem Properties 
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  clauses                                 13
% 35.55/5.00  conjectures                             2
% 35.55/5.00  EPR                                     1
% 35.55/5.00  Horn                                    13
% 35.55/5.00  unary                                   7
% 35.55/5.00  binary                                  6
% 35.55/5.00  lits                                    19
% 35.55/5.00  lits eq                                 9
% 35.55/5.00  fd_pure                                 0
% 35.55/5.00  fd_pseudo                               0
% 35.55/5.00  fd_cond                                 0
% 35.55/5.00  fd_pseudo_cond                          0
% 35.55/5.00  AC symbols                              1
% 35.55/5.00  
% 35.55/5.00  ------ Input Options Time Limit: Unbounded
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  ------ 
% 35.55/5.00  Current options:
% 35.55/5.00  ------ 
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  ------ Proving...
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  % SZS status Theorem for theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  fof(f1,axiom,(
% 35.55/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f19,plain,(
% 35.55/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f1])).
% 35.55/5.00  
% 35.55/5.00  fof(f9,axiom,(
% 35.55/5.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f29,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f9])).
% 35.55/5.00  
% 35.55/5.00  fof(f4,axiom,(
% 35.55/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f24,plain,(
% 35.55/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.55/5.00    inference(cnf_transformation,[],[f4])).
% 35.55/5.00  
% 35.55/5.00  fof(f36,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 35.55/5.00    inference(definition_unfolding,[],[f29,f24])).
% 35.55/5.00  
% 35.55/5.00  fof(f2,axiom,(
% 35.55/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f15,plain,(
% 35.55/5.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.55/5.00    inference(nnf_transformation,[],[f2])).
% 35.55/5.00  
% 35.55/5.00  fof(f20,plain,(
% 35.55/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f15])).
% 35.55/5.00  
% 35.55/5.00  fof(f11,conjecture,(
% 35.55/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f12,negated_conjecture,(
% 35.55/5.00    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 35.55/5.00    inference(negated_conjecture,[],[f11])).
% 35.55/5.00  
% 35.55/5.00  fof(f14,plain,(
% 35.55/5.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 35.55/5.00    inference(ennf_transformation,[],[f12])).
% 35.55/5.00  
% 35.55/5.00  fof(f17,plain,(
% 35.55/5.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 35.55/5.00    introduced(choice_axiom,[])).
% 35.55/5.00  
% 35.55/5.00  fof(f18,plain,(
% 35.55/5.00    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 35.55/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 35.55/5.00  
% 35.55/5.00  fof(f31,plain,(
% 35.55/5.00    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 35.55/5.00    inference(cnf_transformation,[],[f18])).
% 35.55/5.00  
% 35.55/5.00  fof(f37,plain,(
% 35.55/5.00    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 35.55/5.00    inference(definition_unfolding,[],[f31,f24])).
% 35.55/5.00  
% 35.55/5.00  fof(f5,axiom,(
% 35.55/5.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f25,plain,(
% 35.55/5.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f5])).
% 35.55/5.00  
% 35.55/5.00  fof(f6,axiom,(
% 35.55/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f13,plain,(
% 35.55/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.55/5.00    inference(ennf_transformation,[],[f6])).
% 35.55/5.00  
% 35.55/5.00  fof(f26,plain,(
% 35.55/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f13])).
% 35.55/5.00  
% 35.55/5.00  fof(f7,axiom,(
% 35.55/5.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f27,plain,(
% 35.55/5.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 35.55/5.00    inference(cnf_transformation,[],[f7])).
% 35.55/5.00  
% 35.55/5.00  fof(f8,axiom,(
% 35.55/5.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f28,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f8])).
% 35.55/5.00  
% 35.55/5.00  fof(f35,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 35.55/5.00    inference(definition_unfolding,[],[f28,f24])).
% 35.55/5.00  
% 35.55/5.00  fof(f3,axiom,(
% 35.55/5.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f16,plain,(
% 35.55/5.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 35.55/5.00    inference(nnf_transformation,[],[f3])).
% 35.55/5.00  
% 35.55/5.00  fof(f22,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f16])).
% 35.55/5.00  
% 35.55/5.00  fof(f34,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.55/5.00    inference(definition_unfolding,[],[f22,f24])).
% 35.55/5.00  
% 35.55/5.00  fof(f10,axiom,(
% 35.55/5.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 35.55/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f30,plain,(
% 35.55/5.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f10])).
% 35.55/5.00  
% 35.55/5.00  fof(f21,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.55/5.00    inference(cnf_transformation,[],[f15])).
% 35.55/5.00  
% 35.55/5.00  fof(f32,plain,(
% 35.55/5.00    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 35.55/5.00    inference(cnf_transformation,[],[f18])).
% 35.55/5.00  
% 35.55/5.00  cnf(c_0,plain,
% 35.55/5.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.55/5.00      inference(cnf_transformation,[],[f19]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_9,plain,
% 35.55/5.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 35.55/5.00      inference(cnf_transformation,[],[f36]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_375,plain,
% 35.55/5.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_2,plain,
% 35.55/5.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 35.55/5.00      inference(cnf_transformation,[],[f20]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_380,plain,
% 35.55/5.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 35.55/5.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_1910,plain,
% 35.55/5.00      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_375,c_380]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_155288,plain,
% 35.55/5.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_1910,c_0]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_156726,plain,
% 35.55/5.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_0,c_155288]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_12,negated_conjecture,
% 35.55/5.00      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 35.55/5.00      inference(cnf_transformation,[],[f37]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_5,plain,
% 35.55/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.55/5.00      inference(cnf_transformation,[],[f25]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_124,negated_conjecture,
% 35.55/5.00      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.55/5.00      inference(theory_normalisation,[status(thm)],[c_12,c_5,c_0]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_373,plain,
% 35.55/5.00      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_124]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_6,plain,
% 35.55/5.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.55/5.00      inference(cnf_transformation,[],[f26]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_377,plain,
% 35.55/5.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_1777,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_373,c_377]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_429,plain,
% 35.55/5.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_2293,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(X0,sK0) ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_1777,c_429]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_159247,plain,
% 35.55/5.00      ( k3_xboole_0(sK2,sK0) = k3_xboole_0(sK0,k1_xboole_0) ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_156726,c_2293]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_7,plain,
% 35.55/5.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.55/5.00      inference(cnf_transformation,[],[f27]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_159444,plain,
% 35.55/5.00      ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
% 35.55/5.00      inference(demodulation,[status(thm)],[c_159247,c_7]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_8,plain,
% 35.55/5.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 35.55/5.00      inference(cnf_transformation,[],[f35]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_376,plain,
% 35.55/5.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_954,plain,
% 35.55/5.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_0,c_376]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_1778,plain,
% 35.55/5.00      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_954,c_377]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_2283,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(sK0,X0) ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_1777,c_5]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_115198,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(sK0,sK1) ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_1778,c_2283]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_116155,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 35.55/5.00      inference(light_normalisation,[status(thm)],[c_115198,c_1777]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4,plain,
% 35.55/5.00      ( r1_tarski(X0,X1)
% 35.55/5.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.55/5.00      inference(cnf_transformation,[],[f34]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_378,plain,
% 35.55/5.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 35.55/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_118373,plain,
% 35.55/5.00      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 35.55/5.00      | r1_tarski(sK0,sK1) = iProver_top ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_116155,c_378]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_10,plain,
% 35.55/5.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.55/5.00      inference(cnf_transformation,[],[f30]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_118746,plain,
% 35.55/5.00      ( k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) = iProver_top ),
% 35.55/5.00      inference(demodulation,[status(thm)],[c_118373,c_10]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_118747,plain,
% 35.55/5.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 35.55/5.00      inference(equality_resolution_simp,[status(thm)],[c_118746]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_127,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_722,plain,
% 35.55/5.00      ( X0 != X1 | X0 = k3_xboole_0(X2,X3) | k3_xboole_0(X2,X3) != X1 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_127]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_1459,plain,
% 35.55/5.00      ( k3_xboole_0(sK2,sK0) != X0
% 35.55/5.00      | k1_xboole_0 != X0
% 35.55/5.00      | k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_722]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_1460,plain,
% 35.55/5.00      ( k3_xboole_0(sK2,sK0) != k1_xboole_0
% 35.55/5.00      | k1_xboole_0 = k3_xboole_0(sK2,sK0)
% 35.55/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_1459]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_591,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK2,sK0) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_519,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,sK2) != X0
% 35.55/5.00      | k3_xboole_0(sK0,sK2) = k1_xboole_0
% 35.55/5.00      | k1_xboole_0 != X0 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_127]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_590,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK2,sK0)
% 35.55/5.00      | k3_xboole_0(sK0,sK2) = k1_xboole_0
% 35.55/5.00      | k1_xboole_0 != k3_xboole_0(sK2,sK0) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_519]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_1,plain,
% 35.55/5.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.55/5.00      inference(cnf_transformation,[],[f21]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_456,plain,
% 35.55/5.00      ( r1_xboole_0(sK0,sK2) | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_1]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_457,plain,
% 35.55/5.00      ( k3_xboole_0(sK0,sK2) != k1_xboole_0
% 35.55/5.00      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_126,plain,( X0 = X0 ),theory(equality) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_136,plain,
% 35.55/5.00      ( k1_xboole_0 = k1_xboole_0 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_126]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_11,negated_conjecture,
% 35.55/5.00      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 35.55/5.00      inference(cnf_transformation,[],[f32]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_14,plain,
% 35.55/5.00      ( r1_tarski(sK0,sK1) != iProver_top
% 35.55/5.00      | r1_xboole_0(sK0,sK2) != iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(contradiction,plain,
% 35.55/5.00      ( $false ),
% 35.55/5.00      inference(minisat,
% 35.55/5.00                [status(thm)],
% 35.55/5.00                [c_159444,c_118747,c_1460,c_591,c_590,c_457,c_136,c_14]) ).
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  ------                               Statistics
% 35.55/5.00  
% 35.55/5.00  ------ Selected
% 35.55/5.00  
% 35.55/5.00  total_time:                             4.14
% 35.55/5.00  
%------------------------------------------------------------------------------
