%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:01 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of clauses        :   27 (  29 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 (  87 expanded)
%              Number of equality atoms :   70 (  78 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f19,f18,f18])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f20,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_48,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_206,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_371,plain,
    ( X0 != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | X0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_12279,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_36,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) != X3
    | k4_xboole_0(X3,X0) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_37,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_36])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_138,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_37,c_4])).

cnf(c_5,negated_conjecture,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3620,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_138,c_5])).

cnf(c_49,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_489,plain,
    ( X0 != k4_xboole_0(sK0,sK1)
    | X1 != sK2
    | k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_813,plain,
    ( X0 != k4_xboole_0(sK0,sK1)
    | k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_2724,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) != k4_xboole_0(sK0,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_47,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_814,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_302,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_204,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_81,plain,
    ( X0 != X1
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_101,plain,
    ( X0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = X0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_203,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_80,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12279,c_3620,c_2724,c_814,c_302,c_204,c_203,c_80])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.94/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/0.98  
% 3.94/0.98  ------  iProver source info
% 3.94/0.98  
% 3.94/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.94/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/0.98  git: non_committed_changes: false
% 3.94/0.98  git: last_make_outside_of_git: false
% 3.94/0.98  
% 3.94/0.98  ------ 
% 3.94/0.98  ------ Parsing...
% 3.94/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/0.98  ------ Proving...
% 3.94/0.98  ------ Problem Properties 
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  clauses                                 5
% 3.94/0.98  conjectures                             1
% 3.94/0.98  EPR                                     0
% 3.94/0.98  Horn                                    5
% 3.94/0.98  unary                                   5
% 3.94/0.98  binary                                  0
% 3.94/0.98  lits                                    5
% 3.94/0.98  lits eq                                 5
% 3.94/0.98  fd_pure                                 0
% 3.94/0.98  fd_pseudo                               0
% 3.94/0.98  fd_cond                                 0
% 3.94/0.98  fd_pseudo_cond                          0
% 3.94/0.98  AC symbols                              0
% 3.94/0.98  
% 3.94/0.98  ------ Input Options Time Limit: Unbounded
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  ------ 
% 3.94/0.98  Current options:
% 3.94/0.98  ------ 
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  ------ Proving...
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  % SZS status Theorem for theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  fof(f1,axiom,(
% 3.94/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.94/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f14,plain,(
% 3.94/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.94/0.98    inference(cnf_transformation,[],[f1])).
% 3.94/0.98  
% 3.94/0.98  fof(f2,axiom,(
% 3.94/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.94/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f9,plain,(
% 3.94/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 3.94/0.98    inference(unused_predicate_definition_removal,[],[f2])).
% 3.94/0.98  
% 3.94/0.98  fof(f10,plain,(
% 3.94/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 3.94/0.98    inference(ennf_transformation,[],[f9])).
% 3.94/0.98  
% 3.94/0.98  fof(f15,plain,(
% 3.94/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.94/0.98    inference(cnf_transformation,[],[f10])).
% 3.94/0.98  
% 3.94/0.98  fof(f6,axiom,(
% 3.94/0.98    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.94/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f19,plain,(
% 3.94/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.94/0.98    inference(cnf_transformation,[],[f6])).
% 3.94/0.98  
% 3.94/0.98  fof(f5,axiom,(
% 3.94/0.98    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.94/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f18,plain,(
% 3.94/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.94/0.98    inference(cnf_transformation,[],[f5])).
% 3.94/0.98  
% 3.94/0.98  fof(f21,plain,(
% 3.94/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.94/0.98    inference(definition_unfolding,[],[f19,f18,f18])).
% 3.94/0.98  
% 3.94/0.98  fof(f7,conjecture,(
% 3.94/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 3.94/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f8,negated_conjecture,(
% 3.94/0.98    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 3.94/0.98    inference(negated_conjecture,[],[f7])).
% 3.94/0.98  
% 3.94/0.98  fof(f11,plain,(
% 3.94/0.98    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 3.94/0.98    inference(ennf_transformation,[],[f8])).
% 3.94/0.98  
% 3.94/0.98  fof(f12,plain,(
% 3.94/0.98    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 3.94/0.98    introduced(choice_axiom,[])).
% 3.94/0.98  
% 3.94/0.98  fof(f13,plain,(
% 3.94/0.98    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 3.94/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 3.94/0.98  
% 3.94/0.98  fof(f20,plain,(
% 3.94/0.98    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 3.94/0.98    inference(cnf_transformation,[],[f13])).
% 3.94/0.98  
% 3.94/0.98  fof(f22,plain,(
% 3.94/0.98    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))),
% 3.94/0.98    inference(definition_unfolding,[],[f20,f18])).
% 3.94/0.98  
% 3.94/0.98  fof(f3,axiom,(
% 3.94/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.94/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f16,plain,(
% 3.94/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.94/0.98    inference(cnf_transformation,[],[f3])).
% 3.94/0.98  
% 3.94/0.98  fof(f4,axiom,(
% 3.94/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.94/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f17,plain,(
% 3.94/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.94/0.98    inference(cnf_transformation,[],[f4])).
% 3.94/0.98  
% 3.94/0.98  cnf(c_48,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_206,plain,
% 3.94/0.98      ( X0 != X1
% 3.94/0.98      | X0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1 ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_48]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_371,plain,
% 3.94/0.98      ( X0 != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 3.94/0.98      | X0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_206]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_12279,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 3.94/0.98      | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_371]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_0,plain,
% 3.94/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.94/0.98      inference(cnf_transformation,[],[f14]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_1,plain,
% 3.94/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.94/0.98      inference(cnf_transformation,[],[f15]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_36,plain,
% 3.94/0.98      ( X0 != X1
% 3.94/0.98      | k4_xboole_0(X1,X2) != X3
% 3.94/0.98      | k4_xboole_0(X3,X0) = k1_xboole_0 ),
% 3.94/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_37,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.94/0.98      inference(unflattening,[status(thm)],[c_36]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_4,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.94/0.98      inference(cnf_transformation,[],[f21]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_138,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
% 3.94/0.98      inference(superposition,[status(thm)],[c_37,c_4]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_5,negated_conjecture,
% 3.94/0.98      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
% 3.94/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_3620,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.94/0.98      inference(superposition,[status(thm)],[c_138,c_5]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_49,plain,
% 3.94/0.98      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 3.94/0.98      theory(equality) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_489,plain,
% 3.94/0.98      ( X0 != k4_xboole_0(sK0,sK1)
% 3.94/0.98      | X1 != sK2
% 3.94/0.98      | k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_49]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_813,plain,
% 3.94/0.98      ( X0 != k4_xboole_0(sK0,sK1)
% 3.94/0.98      | k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 3.94/0.98      | sK2 != sK2 ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_489]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_2724,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 3.94/0.98      | k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) != k4_xboole_0(sK0,sK1)
% 3.94/0.98      | sK2 != sK2 ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_813]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_47,plain,( X0 = X0 ),theory(equality) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_814,plain,
% 3.94/0.98      ( sK2 = sK2 ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_47]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_2,plain,
% 3.94/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.94/0.98      inference(cnf_transformation,[],[f16]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_302,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_3,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.94/0.98      inference(cnf_transformation,[],[f17]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_204,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_81,plain,
% 3.94/0.98      ( X0 != X1
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = X0 ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_48]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_101,plain,
% 3.94/0.98      ( X0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = X0
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_81]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_203,plain,
% 3.94/0.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 3.94/0.98      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_101]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(c_80,plain,
% 3.94/0.98      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.94/0.98      inference(instantiation,[status(thm)],[c_47]) ).
% 3.94/0.98  
% 3.94/0.98  cnf(contradiction,plain,
% 3.94/0.98      ( $false ),
% 3.94/0.98      inference(minisat,
% 3.94/0.98                [status(thm)],
% 3.94/0.98                [c_12279,c_3620,c_2724,c_814,c_302,c_204,c_203,c_80]) ).
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  ------                               Statistics
% 3.94/0.98  
% 3.94/0.98  ------ Selected
% 3.94/0.98  
% 3.94/0.98  total_time:                             0.376
% 3.94/0.98  
%------------------------------------------------------------------------------
