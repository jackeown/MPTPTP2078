%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:00 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of clauses        :   42 (  48 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 234 expanded)
%              Number of equality atoms :   69 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f10])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f21,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_32692,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),X0)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),X1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_32967,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_32692])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_30595,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_31036,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_30595])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_26061,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k2_xboole_0(sK1,sK0))
    | k2_xboole_0(sK1,sK0) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_30544,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k2_xboole_0(sK1,sK0))
    | k2_xboole_0(sK1,sK0) != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_26061])).

cnf(c_30545,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k2_xboole_0(sK1,sK0))
    | k2_xboole_0(sK1,sK0) != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_30544])).

cnf(c_30577,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK0))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,X0))
    | k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_30545])).

cnf(c_31014,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK0))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_30577])).

cnf(c_92,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_23362,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_23926,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23362])).

cnf(c_23927,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_23926])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_5801,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5156,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1996,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2000,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2394,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1996,c_2000])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_1999,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2275,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1999])).

cnf(c_3262,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_2275])).

cnf(c_3323,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3262])).

cnf(c_3029,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3054,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK0))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3029])).

cnf(c_2435,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != X0
    | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_2763,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_2327,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1210,plain,
    ( k4_xboole_0(sK0,sK1) != X0
    | k4_xboole_0(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_1220,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_1221,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_1220])).

cnf(c_939,plain,
    ( r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32967,c_31036,c_31014,c_23927,c_5801,c_5156,c_3323,c_3054,c_2763,c_2327,c_1221,c_939,c_6,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:52:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.08/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.08/1.49  
% 8.08/1.49  ------  iProver source info
% 8.08/1.49  
% 8.08/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.08/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.08/1.49  git: non_committed_changes: false
% 8.08/1.49  git: last_make_outside_of_git: false
% 8.08/1.49  
% 8.08/1.49  ------ 
% 8.08/1.49  ------ Parsing...
% 8.08/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  ------ Proving...
% 8.08/1.49  ------ Problem Properties 
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  clauses                                 9
% 8.08/1.49  conjectures                             3
% 8.08/1.49  EPR                                     3
% 8.08/1.49  Horn                                    9
% 8.08/1.49  unary                                   6
% 8.08/1.49  binary                                  2
% 8.08/1.49  lits                                    14
% 8.08/1.49  lits eq                                 5
% 8.08/1.49  fd_pure                                 0
% 8.08/1.49  fd_pseudo                               0
% 8.08/1.49  fd_cond                                 1
% 8.08/1.49  fd_pseudo_cond                          0
% 8.08/1.49  AC symbols                              0
% 8.08/1.49  
% 8.08/1.49  ------ Input Options Time Limit: Unbounded
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing...
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 8.08/1.49  Current options:
% 8.08/1.49  ------ 
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing...
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  % SZS status Theorem for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  fof(f4,axiom,(
% 8.08/1.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 8.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f8,plain,(
% 8.08/1.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 8.08/1.49    inference(ennf_transformation,[],[f4])).
% 8.08/1.49  
% 8.08/1.49  fof(f9,plain,(
% 8.08/1.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 8.08/1.49    inference(flattening,[],[f8])).
% 8.08/1.49  
% 8.08/1.49  fof(f19,plain,(
% 8.08/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f9])).
% 8.08/1.49  
% 8.08/1.49  fof(f5,axiom,(
% 8.08/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f20,plain,(
% 8.08/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.08/1.49    inference(cnf_transformation,[],[f5])).
% 8.08/1.49  
% 8.08/1.49  fof(f1,axiom,(
% 8.08/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f15,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f1])).
% 8.08/1.49  
% 8.08/1.49  fof(f3,axiom,(
% 8.08/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 8.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f18,plain,(
% 8.08/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f3])).
% 8.08/1.49  
% 8.08/1.49  fof(f6,conjecture,(
% 8.08/1.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 8.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f7,negated_conjecture,(
% 8.08/1.49    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 8.08/1.49    inference(negated_conjecture,[],[f6])).
% 8.08/1.49  
% 8.08/1.49  fof(f10,plain,(
% 8.08/1.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 8.08/1.49    inference(ennf_transformation,[],[f7])).
% 8.08/1.49  
% 8.08/1.49  fof(f11,plain,(
% 8.08/1.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 8.08/1.49    inference(flattening,[],[f10])).
% 8.08/1.49  
% 8.08/1.49  fof(f13,plain,(
% 8.08/1.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 8.08/1.49    introduced(choice_axiom,[])).
% 8.08/1.49  
% 8.08/1.49  fof(f14,plain,(
% 8.08/1.49    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 8.08/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 8.08/1.49  
% 8.08/1.49  fof(f21,plain,(
% 8.08/1.49    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 8.08/1.49    inference(cnf_transformation,[],[f14])).
% 8.08/1.49  
% 8.08/1.49  fof(f2,axiom,(
% 8.08/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 8.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f12,plain,(
% 8.08/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 8.08/1.49    inference(nnf_transformation,[],[f2])).
% 8.08/1.49  
% 8.08/1.49  fof(f17,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f12])).
% 8.08/1.49  
% 8.08/1.49  fof(f16,plain,(
% 8.08/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 8.08/1.49    inference(cnf_transformation,[],[f12])).
% 8.08/1.49  
% 8.08/1.49  fof(f23,plain,(
% 8.08/1.49    ~r1_tarski(sK0,sK1)),
% 8.08/1.49    inference(cnf_transformation,[],[f14])).
% 8.08/1.49  
% 8.08/1.49  fof(f22,plain,(
% 8.08/1.49    r1_xboole_0(sK0,sK2)),
% 8.08/1.49    inference(cnf_transformation,[],[f14])).
% 8.08/1.49  
% 8.08/1.49  cnf(c_4,plain,
% 8.08/1.49      ( ~ r1_xboole_0(X0,X1)
% 8.08/1.49      | ~ r1_tarski(X2,X0)
% 8.08/1.49      | ~ r1_tarski(X2,X1)
% 8.08/1.49      | k1_xboole_0 = X2 ),
% 8.08/1.49      inference(cnf_transformation,[],[f19]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_32692,plain,
% 8.08/1.49      ( ~ r1_xboole_0(X0,X1)
% 8.08/1.49      | ~ r1_tarski(k4_xboole_0(sK0,sK1),X0)
% 8.08/1.49      | ~ r1_tarski(k4_xboole_0(sK0,sK1),X1)
% 8.08/1.49      | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_32967,plain,
% 8.08/1.49      ( ~ r1_xboole_0(sK0,sK2)
% 8.08/1.49      | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
% 8.08/1.49      | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
% 8.08/1.49      | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_32692]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5,plain,
% 8.08/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f20]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_30595,plain,
% 8.08/1.49      ( r1_tarski(sK0,k2_xboole_0(sK0,X0)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_31036,plain,
% 8.08/1.49      ( r1_tarski(sK0,k2_xboole_0(sK0,sK1)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_30595]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_95,plain,
% 8.08/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.08/1.49      theory(equality) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_26061,plain,
% 8.08/1.49      ( ~ r1_tarski(X0,X1)
% 8.08/1.49      | r1_tarski(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | k2_xboole_0(sK1,sK0) != X1
% 8.08/1.49      | sK0 != X0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_95]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_30544,plain,
% 8.08/1.49      ( ~ r1_tarski(sK0,X0)
% 8.08/1.49      | r1_tarski(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | k2_xboole_0(sK1,sK0) != X0
% 8.08/1.49      | sK0 != sK0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_26061]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_30545,plain,
% 8.08/1.49      ( ~ r1_tarski(sK0,X0)
% 8.08/1.49      | r1_tarski(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | k2_xboole_0(sK1,sK0) != X0 ),
% 8.08/1.49      inference(equality_resolution_simp,[status(thm)],[c_30544]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_30577,plain,
% 8.08/1.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | ~ r1_tarski(sK0,k2_xboole_0(sK0,X0))
% 8.08/1.49      | k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,X0) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_30545]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_31014,plain,
% 8.08/1.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
% 8.08/1.49      | k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_30577]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_92,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_23362,plain,
% 8.08/1.49      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != X0
% 8.08/1.49      | k1_xboole_0 != X0
% 8.08/1.49      | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_92]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_23926,plain,
% 8.08/1.49      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != k1_xboole_0
% 8.08/1.49      | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_23362]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_23927,plain,
% 8.08/1.49      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != k1_xboole_0
% 8.08/1.49      | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
% 8.08/1.49      inference(equality_resolution_simp,[status(thm)],[c_23926]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_0,plain,
% 8.08/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f15]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5801,plain,
% 8.08/1.49      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3,plain,
% 8.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f18]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5156,plain,
% 8.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_8,negated_conjecture,
% 8.08/1.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f21]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1996,plain,
% 8.08/1.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1,plain,
% 8.08/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 8.08/1.49      inference(cnf_transformation,[],[f17]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2000,plain,
% 8.08/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 8.08/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2394,plain,
% 8.08/1.49      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_1996,c_2000]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2,plain,
% 8.08/1.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 8.08/1.49      inference(cnf_transformation,[],[f16]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1999,plain,
% 8.08/1.49      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 8.08/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2275,plain,
% 8.08/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
% 8.08/1.49      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_3,c_1999]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3262,plain,
% 8.08/1.49      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_2394,c_2275]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3323,plain,
% 8.08/1.49      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
% 8.08/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3262]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3029,plain,
% 8.08/1.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 8.08/1.49      | k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3054,plain,
% 8.08/1.49      ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_3029]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2435,plain,
% 8.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != X0
% 8.08/1.49      | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0
% 8.08/1.49      | k1_xboole_0 != X0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_92]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2763,plain,
% 8.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
% 8.08/1.49      | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0
% 8.08/1.49      | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_2435]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2327,plain,
% 8.08/1.49      ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
% 8.08/1.49      | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k1_xboole_0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1210,plain,
% 8.08/1.49      ( k4_xboole_0(sK0,sK1) != X0
% 8.08/1.49      | k4_xboole_0(sK0,sK1) = k1_xboole_0
% 8.08/1.49      | k1_xboole_0 != X0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_92]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1220,plain,
% 8.08/1.49      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
% 8.08/1.49      | k4_xboole_0(sK0,sK1) = k1_xboole_0
% 8.08/1.49      | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1210]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1221,plain,
% 8.08/1.49      ( k4_xboole_0(sK0,sK1) = k1_xboole_0
% 8.08/1.49      | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
% 8.08/1.49      inference(equality_resolution_simp,[status(thm)],[c_1220]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_939,plain,
% 8.08/1.49      ( r1_tarski(sK0,sK1) | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6,negated_conjecture,
% 8.08/1.49      ( ~ r1_tarski(sK0,sK1) ),
% 8.08/1.49      inference(cnf_transformation,[],[f23]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_7,negated_conjecture,
% 8.08/1.49      ( r1_xboole_0(sK0,sK2) ),
% 8.08/1.49      inference(cnf_transformation,[],[f22]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(contradiction,plain,
% 8.08/1.49      ( $false ),
% 8.08/1.49      inference(minisat,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_32967,c_31036,c_31014,c_23927,c_5801,c_5156,c_3323,
% 8.08/1.49                 c_3054,c_2763,c_2327,c_1221,c_939,c_6,c_7]) ).
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  ------                               Statistics
% 8.08/1.49  
% 8.08/1.49  ------ Selected
% 8.08/1.49  
% 8.08/1.49  total_time:                             0.967
% 8.08/1.49  
%------------------------------------------------------------------------------
