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
% DateTime   : Thu Dec  3 11:25:58 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 194 expanded)
%              Number of clauses        :   31 (  62 expanded)
%              Number of leaves         :    8 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  109 ( 344 expanded)
%              Number of equality atoms :   44 ( 130 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f23,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f28,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f23,f17])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f20,f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f21,f17,f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f22,f17])).

fof(f24,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_808,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_809,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_811,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1027,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_811])).

cnf(c_10840,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_1027])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_810,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11943,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_10840,c_810])).

cnf(c_863,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_808,c_810])).

cnf(c_3,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_905,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_809])).

cnf(c_922,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_905])).

cnf(c_1122,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_922,c_810])).

cnf(c_11966,plain,
    ( k3_xboole_0(sK0,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_11943,c_1122])).

cnf(c_8316,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | r1_tarski(X0,sK1)
    | ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8321,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_8316])).

cnf(c_2647,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2070,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1122,c_3])).

cnf(c_2096,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_2070,c_3])).

cnf(c_2300,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_863,c_2096])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_72,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_73,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_72])).

cnf(c_806,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_2530,plain,
    ( k3_xboole_0(sK0,sK0) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2300,c_806])).

cnf(c_2531,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(sK0,sK0) != sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2530])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11966,c_8321,c_2647,c_2531,c_6])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:26:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.74/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.99  
% 3.74/0.99  ------  iProver source info
% 3.74/0.99  
% 3.74/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.99  git: non_committed_changes: false
% 3.74/0.99  git: last_make_outside_of_git: false
% 3.74/0.99  
% 3.74/0.99  ------ 
% 3.74/0.99  ------ Parsing...
% 3.74/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  ------ Proving...
% 3.74/0.99  ------ Problem Properties 
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  clauses                                 6
% 3.74/0.99  conjectures                             1
% 3.74/0.99  EPR                                     1
% 3.74/0.99  Horn                                    6
% 3.74/0.99  unary                                   3
% 3.74/0.99  binary                                  2
% 3.74/0.99  lits                                    10
% 3.74/0.99  lits eq                                 3
% 3.74/0.99  fd_pure                                 0
% 3.74/0.99  fd_pseudo                               0
% 3.74/0.99  fd_cond                                 0
% 3.74/0.99  fd_pseudo_cond                          0
% 3.74/0.99  AC symbols                              0
% 3.74/0.99  
% 3.74/0.99  ------ Input Options Time Limit: Unbounded
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.74/0.99  Current options:
% 3.74/0.99  ------ 
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS status Theorem for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  fof(f7,conjecture,(
% 3.74/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f8,negated_conjecture,(
% 3.74/0.99    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.74/0.99    inference(negated_conjecture,[],[f7])).
% 3.74/0.99  
% 3.74/0.99  fof(f14,plain,(
% 3.74/0.99    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.74/0.99    inference(ennf_transformation,[],[f8])).
% 3.74/0.99  
% 3.74/0.99  fof(f15,plain,(
% 3.74/0.99    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f16,plain,(
% 3.74/0.99    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 3.74/0.99  
% 3.74/0.99  fof(f23,plain,(
% 3.74/0.99    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.74/0.99    inference(cnf_transformation,[],[f16])).
% 3.74/0.99  
% 3.74/0.99  fof(f1,axiom,(
% 3.74/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f17,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f1])).
% 3.74/0.99  
% 3.74/0.99  fof(f28,plain,(
% 3.74/0.99    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 3.74/0.99    inference(definition_unfolding,[],[f23,f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f4,axiom,(
% 3.74/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f20,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f4])).
% 3.74/0.99  
% 3.74/0.99  fof(f25,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.74/0.99    inference(definition_unfolding,[],[f20,f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f2,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f10,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.74/0.99    inference(ennf_transformation,[],[f2])).
% 3.74/0.99  
% 3.74/0.99  fof(f11,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.74/0.99    inference(flattening,[],[f10])).
% 3.74/0.99  
% 3.74/0.99  fof(f18,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f11])).
% 3.74/0.99  
% 3.74/0.99  fof(f3,axiom,(
% 3.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f12,plain,(
% 3.74/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.74/0.99    inference(ennf_transformation,[],[f3])).
% 3.74/0.99  
% 3.74/0.99  fof(f19,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f12])).
% 3.74/0.99  
% 3.74/0.99  fof(f5,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f21,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f5])).
% 3.74/0.99  
% 3.74/0.99  fof(f26,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 3.74/0.99    inference(definition_unfolding,[],[f21,f17,f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f6,axiom,(
% 3.74/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f9,plain,(
% 3.74/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 3.74/0.99    inference(unused_predicate_definition_removal,[],[f6])).
% 3.74/0.99  
% 3.74/0.99  fof(f13,plain,(
% 3.74/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 3.74/0.99    inference(ennf_transformation,[],[f9])).
% 3.74/0.99  
% 3.74/0.99  fof(f22,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.74/0.99    inference(cnf_transformation,[],[f13])).
% 3.74/0.99  
% 3.74/0.99  fof(f27,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 3.74/0.99    inference(definition_unfolding,[],[f22,f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f24,plain,(
% 3.74/0.99    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 3.74/0.99    inference(cnf_transformation,[],[f16])).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6,negated_conjecture,
% 3.74/0.99      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 3.74/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_808,plain,
% 3.74/0.99      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2,plain,
% 3.74/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_809,plain,
% 3.74/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_0,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f18]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_811,plain,
% 3.74/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.74/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.74/0.99      | r1_tarski(X2,X1) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1027,plain,
% 3.74/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.74/0.99      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_809,c_811]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10840,plain,
% 3.74/0.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_808,c_1027]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.74/0.99      inference(cnf_transformation,[],[f19]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_810,plain,
% 3.74/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11943,plain,
% 3.74/0.99      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_10840,c_810]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_863,plain,
% 3.74/0.99      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_808,c_810]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3,plain,
% 3.74/0.99      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.74/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_905,plain,
% 3.74/0.99      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3,c_809]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_922,plain,
% 3.74/0.99      ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_863,c_905]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1122,plain,
% 3.74/0.99      ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_922,c_810]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11966,plain,
% 3.74/0.99      ( k3_xboole_0(sK0,sK0) = sK0 ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_11943,c_1122]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8316,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 3.74/0.99      | r1_tarski(X0,sK1)
% 3.74/0.99      | ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8321,plain,
% 3.74/0.99      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
% 3.74/0.99      | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 3.74/0.99      | r1_tarski(sK0,sK1) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_8316]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2647,plain,
% 3.74/0.99      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2070,plain,
% 3.74/0.99      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_1122,c_3]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2096,plain,
% 3.74/0.99      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_2070,c_3]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2300,plain,
% 3.74/0.99      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK0) ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_863,c_2096]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4,plain,
% 3.74/0.99      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 3.74/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5,negated_conjecture,
% 3.74/0.99      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_72,plain,
% 3.74/0.99      ( ~ r1_tarski(sK0,sK1)
% 3.74/0.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 3.74/0.99      | sK2 != X1
% 3.74/0.99      | sK0 != X0 ),
% 3.74/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_73,plain,
% 3.74/0.99      ( ~ r1_tarski(sK0,sK1)
% 3.74/0.99      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != sK0 ),
% 3.74/0.99      inference(unflattening,[status(thm)],[c_72]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_806,plain,
% 3.74/0.99      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != sK0
% 3.74/0.99      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2530,plain,
% 3.74/0.99      ( k3_xboole_0(sK0,sK0) != sK0 | r1_tarski(sK0,sK1) != iProver_top ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_2300,c_806]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2531,plain,
% 3.74/0.99      ( ~ r1_tarski(sK0,sK1) | k3_xboole_0(sK0,sK0) != sK0 ),
% 3.74/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2530]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(contradiction,plain,
% 3.74/0.99      ( $false ),
% 3.74/0.99      inference(minisat,[status(thm)],[c_11966,c_8321,c_2647,c_2531,c_6]) ).
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  ------                               Statistics
% 3.74/0.99  
% 3.74/0.99  ------ Selected
% 3.74/0.99  
% 3.74/0.99  total_time:                             0.423
% 3.74/0.99  
%------------------------------------------------------------------------------
