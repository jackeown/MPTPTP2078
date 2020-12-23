%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:52 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 239 expanded)
%              Number of clauses        :   45 (  85 expanded)
%              Number of leaves         :    8 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  201 ( 775 expanded)
%              Number of equality atoms :  142 ( 541 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 )
   => ( k1_tarski(sK1) != sK0
      & k1_xboole_0 != sK0
      & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k1_tarski(sK1) != sK0
    & k1_xboole_0 != sK0
    & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).

fof(f45,plain,(
    k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f43])).

fof(f46,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f29])).

cnf(c_19,negated_conjecture,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19714,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20034,plain,
    ( r1_tarski(sK0,k1_tarski(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_19714])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_19717,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20268,plain,
    ( k1_tarski(sK1) = sK0
    | r2_xboole_0(sK0,k1_tarski(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20034,c_19717])).

cnf(c_17,negated_conjecture,
    ( k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3844,plain,
    ( r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(resolution,[status(thm)],[c_4,c_19])).

cnf(c_3845,plain,
    ( r1_tarski(sK0,k1_tarski(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3844])).

cnf(c_19785,plain,
    ( ~ r1_tarski(sK0,k1_tarski(sK1))
    | r2_xboole_0(sK0,k1_tarski(sK1))
    | k1_tarski(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19786,plain,
    ( k1_tarski(sK1) = sK0
    | r1_tarski(sK0,k1_tarski(sK1)) != iProver_top
    | r2_xboole_0(sK0,k1_tarski(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19785])).

cnf(c_20445,plain,
    ( r2_xboole_0(sK0,k1_tarski(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20268,c_17,c_3845,c_19786])).

cnf(c_14,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19711,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X2,X0)
    | r2_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19713,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_xboole_0(X2,X0) != iProver_top
    | r2_xboole_0(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20291,plain,
    ( r2_xboole_0(X0,k2_tarski(X1,X2)) = iProver_top
    | r2_xboole_0(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19711,c_19713])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19715,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21043,plain,
    ( r1_tarski(X0,k2_tarski(X1,X2)) = iProver_top
    | r2_xboole_0(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20291,c_19715])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19710,plain,
    ( k2_tarski(X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21725,plain,
    ( k2_tarski(X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | k1_xboole_0 = X2
    | r2_xboole_0(X2,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21043,c_19710])).

cnf(c_22329,plain,
    ( k2_tarski(sK1,X0) = sK0
    | k1_tarski(X0) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20445,c_21725])).

cnf(c_13,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19712,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20290,plain,
    ( r2_xboole_0(X0,k2_tarski(X1,X2)) = iProver_top
    | r2_xboole_0(X0,k1_tarski(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19712,c_19713])).

cnf(c_20690,plain,
    ( r1_tarski(X0,k2_tarski(X1,X2)) = iProver_top
    | r2_xboole_0(X0,k1_tarski(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20290,c_19715])).

cnf(c_21212,plain,
    ( k2_tarski(X0,X1) = X2
    | k1_tarski(X0) = X2
    | k1_tarski(X1) = X2
    | k1_xboole_0 = X2
    | r2_xboole_0(X2,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20690,c_19710])).

cnf(c_22130,plain,
    ( k2_tarski(X0,sK1) = sK0
    | k1_tarski(X0) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20445,c_21212])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_202,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_211,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_203,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1648,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_1649,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_22651,plain,
    ( k2_tarski(X0,sK1) = sK0
    | k1_tarski(X0) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22130,c_18,c_17,c_211,c_1649])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19716,plain,
    ( r2_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_20691,plain,
    ( r2_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20290,c_19716])).

cnf(c_22666,plain,
    ( k1_tarski(X0) = sK0
    | r2_xboole_0(sK0,k1_tarski(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22651,c_20691])).

cnf(c_22782,plain,
    ( k1_tarski(X0) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22329,c_17,c_3845,c_19786,c_22666])).

cnf(c_22811,plain,
    ( sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_22782,c_17])).

cnf(c_22819,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22811])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.71/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/1.49  
% 7.71/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.49  
% 7.71/1.49  ------  iProver source info
% 7.71/1.49  
% 7.71/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.49  git: non_committed_changes: false
% 7.71/1.49  git: last_make_outside_of_git: false
% 7.71/1.49  
% 7.71/1.49  ------ 
% 7.71/1.49  ------ Parsing...
% 7.71/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  ------ Proving...
% 7.71/1.49  ------ Problem Properties 
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  clauses                                 20
% 7.71/1.49  conjectures                             3
% 7.71/1.49  EPR                                     7
% 7.71/1.49  Horn                                    18
% 7.71/1.49  unary                                   9
% 7.71/1.49  binary                                  7
% 7.71/1.49  lits                                    37
% 7.71/1.49  lits eq                                 11
% 7.71/1.49  fd_pure                                 0
% 7.71/1.49  fd_pseudo                               0
% 7.71/1.49  fd_cond                                 1
% 7.71/1.49  fd_pseudo_cond                          2
% 7.71/1.49  AC symbols                              0
% 7.71/1.49  
% 7.71/1.49  ------ Input Options Time Limit: Unbounded
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.71/1.49  Current options:
% 7.71/1.49  ------ 
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  % SZS status Theorem for theBenchmark.p
% 7.71/1.49  
% 7.71/1.49   Resolution empty clause
% 7.71/1.49  
% 7.71/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.49  
% 7.71/1.49  fof(f10,conjecture,(
% 7.71/1.49    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f11,negated_conjecture,(
% 7.71/1.49    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 7.71/1.49    inference(negated_conjecture,[],[f10])).
% 7.71/1.49  
% 7.71/1.49  fof(f20,plain,(
% 7.71/1.49    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 7.71/1.49    inference(ennf_transformation,[],[f11])).
% 7.71/1.49  
% 7.71/1.49  fof(f26,plain,(
% 7.71/1.49    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0) => (k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0)),
% 7.71/1.49    introduced(choice_axiom,[])).
% 7.71/1.49  
% 7.71/1.49  fof(f27,plain,(
% 7.71/1.49    k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0),
% 7.71/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).
% 7.71/1.49  
% 7.71/1.49  fof(f45,plain,(
% 7.71/1.49    k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0),
% 7.71/1.49    inference(cnf_transformation,[],[f27])).
% 7.71/1.49  
% 7.71/1.49  fof(f2,axiom,(
% 7.71/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f23,plain,(
% 7.71/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.71/1.49    inference(nnf_transformation,[],[f2])).
% 7.71/1.49  
% 7.71/1.49  fof(f31,plain,(
% 7.71/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.71/1.49    inference(cnf_transformation,[],[f23])).
% 7.71/1.49  
% 7.71/1.49  fof(f1,axiom,(
% 7.71/1.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f21,plain,(
% 7.71/1.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 7.71/1.49    inference(nnf_transformation,[],[f1])).
% 7.71/1.49  
% 7.71/1.49  fof(f22,plain,(
% 7.71/1.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 7.71/1.49    inference(flattening,[],[f21])).
% 7.71/1.49  
% 7.71/1.49  fof(f30,plain,(
% 7.71/1.49    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f22])).
% 7.71/1.49  
% 7.71/1.49  fof(f47,plain,(
% 7.71/1.49    k1_tarski(sK1) != sK0),
% 7.71/1.49    inference(cnf_transformation,[],[f27])).
% 7.71/1.49  
% 7.71/1.49  fof(f9,axiom,(
% 7.71/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f19,plain,(
% 7.71/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.71/1.49    inference(ennf_transformation,[],[f9])).
% 7.71/1.49  
% 7.71/1.49  fof(f24,plain,(
% 7.71/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.71/1.49    inference(nnf_transformation,[],[f19])).
% 7.71/1.49  
% 7.71/1.49  fof(f25,plain,(
% 7.71/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.71/1.49    inference(flattening,[],[f24])).
% 7.71/1.49  
% 7.71/1.49  fof(f42,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 7.71/1.49    inference(cnf_transformation,[],[f25])).
% 7.71/1.49  
% 7.71/1.49  fof(f51,plain,(
% 7.71/1.49    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 7.71/1.49    inference(equality_resolution,[],[f42])).
% 7.71/1.49  
% 7.71/1.49  fof(f6,axiom,(
% 7.71/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f14,plain,(
% 7.71/1.49    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 7.71/1.49    inference(ennf_transformation,[],[f6])).
% 7.71/1.49  
% 7.71/1.49  fof(f15,plain,(
% 7.71/1.49    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 7.71/1.49    inference(flattening,[],[f14])).
% 7.71/1.49  
% 7.71/1.49  fof(f37,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f15])).
% 7.71/1.49  
% 7.71/1.49  fof(f28,plain,(
% 7.71/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f22])).
% 7.71/1.49  
% 7.71/1.49  fof(f40,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.71/1.49    inference(cnf_transformation,[],[f25])).
% 7.71/1.49  
% 7.71/1.49  fof(f43,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 7.71/1.49    inference(cnf_transformation,[],[f25])).
% 7.71/1.49  
% 7.71/1.49  fof(f50,plain,(
% 7.71/1.49    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 7.71/1.49    inference(equality_resolution,[],[f43])).
% 7.71/1.49  
% 7.71/1.49  fof(f46,plain,(
% 7.71/1.49    k1_xboole_0 != sK0),
% 7.71/1.49    inference(cnf_transformation,[],[f27])).
% 7.71/1.49  
% 7.71/1.49  fof(f29,plain,(
% 7.71/1.49    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f22])).
% 7.71/1.49  
% 7.71/1.49  fof(f48,plain,(
% 7.71/1.49    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 7.71/1.49    inference(equality_resolution,[],[f29])).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19,negated_conjecture,
% 7.71/1.49      ( k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4,plain,
% 7.71/1.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19714,plain,
% 7.71/1.49      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_20034,plain,
% 7.71/1.49      ( r1_tarski(sK0,k1_tarski(sK1)) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_19,c_19714]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_0,plain,
% 7.71/1.49      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19717,plain,
% 7.71/1.49      ( X0 = X1
% 7.71/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.71/1.49      | r2_xboole_0(X1,X0) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_20268,plain,
% 7.71/1.49      ( k1_tarski(sK1) = sK0 | r2_xboole_0(sK0,k1_tarski(sK1)) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_20034,c_19717]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_17,negated_conjecture,
% 7.71/1.49      ( k1_tarski(sK1) != sK0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3844,plain,
% 7.71/1.49      ( r1_tarski(sK0,k1_tarski(sK1)) ),
% 7.71/1.49      inference(resolution,[status(thm)],[c_4,c_19]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3845,plain,
% 7.71/1.49      ( r1_tarski(sK0,k1_tarski(sK1)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_3844]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19785,plain,
% 7.71/1.49      ( ~ r1_tarski(sK0,k1_tarski(sK1))
% 7.71/1.49      | r2_xboole_0(sK0,k1_tarski(sK1))
% 7.71/1.49      | k1_tarski(sK1) = sK0 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19786,plain,
% 7.71/1.49      ( k1_tarski(sK1) = sK0
% 7.71/1.49      | r1_tarski(sK0,k1_tarski(sK1)) != iProver_top
% 7.71/1.49      | r2_xboole_0(sK0,k1_tarski(sK1)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_19785]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_20445,plain,
% 7.71/1.49      ( r2_xboole_0(sK0,k1_tarski(sK1)) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_20268,c_17,c_3845,c_19786]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14,plain,
% 7.71/1.49      ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19711,plain,
% 7.71/1.49      ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9,plain,
% 7.71/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_xboole_0(X2,X0) | r2_xboole_0(X2,X1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19713,plain,
% 7.71/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.71/1.49      | r2_xboole_0(X2,X0) != iProver_top
% 7.71/1.49      | r2_xboole_0(X2,X1) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_20291,plain,
% 7.71/1.49      ( r2_xboole_0(X0,k2_tarski(X1,X2)) = iProver_top
% 7.71/1.49      | r2_xboole_0(X0,k1_tarski(X1)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_19711,c_19713]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2,plain,
% 7.71/1.49      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19715,plain,
% 7.71/1.49      ( r1_tarski(X0,X1) = iProver_top | r2_xboole_0(X0,X1) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_21043,plain,
% 7.71/1.49      ( r1_tarski(X0,k2_tarski(X1,X2)) = iProver_top
% 7.71/1.49      | r2_xboole_0(X0,k1_tarski(X1)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_20291,c_19715]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_16,plain,
% 7.71/1.49      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
% 7.71/1.49      | k2_tarski(X1,X2) = X0
% 7.71/1.49      | k1_tarski(X2) = X0
% 7.71/1.49      | k1_tarski(X1) = X0
% 7.71/1.49      | k1_xboole_0 = X0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19710,plain,
% 7.71/1.49      ( k2_tarski(X0,X1) = X2
% 7.71/1.49      | k1_tarski(X1) = X2
% 7.71/1.49      | k1_tarski(X0) = X2
% 7.71/1.49      | k1_xboole_0 = X2
% 7.71/1.49      | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_21725,plain,
% 7.71/1.49      ( k2_tarski(X0,X1) = X2
% 7.71/1.49      | k1_tarski(X1) = X2
% 7.71/1.49      | k1_tarski(X0) = X2
% 7.71/1.49      | k1_xboole_0 = X2
% 7.71/1.49      | r2_xboole_0(X2,k1_tarski(X0)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_21043,c_19710]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22329,plain,
% 7.71/1.49      ( k2_tarski(sK1,X0) = sK0
% 7.71/1.49      | k1_tarski(X0) = sK0
% 7.71/1.49      | k1_tarski(sK1) = sK0
% 7.71/1.49      | sK0 = k1_xboole_0 ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_20445,c_21725]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_13,plain,
% 7.71/1.49      ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19712,plain,
% 7.71/1.49      ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_20290,plain,
% 7.71/1.49      ( r2_xboole_0(X0,k2_tarski(X1,X2)) = iProver_top
% 7.71/1.49      | r2_xboole_0(X0,k1_tarski(X2)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_19712,c_19713]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_20690,plain,
% 7.71/1.49      ( r1_tarski(X0,k2_tarski(X1,X2)) = iProver_top
% 7.71/1.49      | r2_xboole_0(X0,k1_tarski(X2)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_20290,c_19715]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_21212,plain,
% 7.71/1.49      ( k2_tarski(X0,X1) = X2
% 7.71/1.49      | k1_tarski(X0) = X2
% 7.71/1.49      | k1_tarski(X1) = X2
% 7.71/1.49      | k1_xboole_0 = X2
% 7.71/1.49      | r2_xboole_0(X2,k1_tarski(X1)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_20690,c_19710]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22130,plain,
% 7.71/1.49      ( k2_tarski(X0,sK1) = sK0
% 7.71/1.49      | k1_tarski(X0) = sK0
% 7.71/1.49      | k1_tarski(sK1) = sK0
% 7.71/1.49      | sK0 = k1_xboole_0 ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_20445,c_21212]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18,negated_conjecture,
% 7.71/1.49      ( k1_xboole_0 != sK0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_202,plain,( X0 = X0 ),theory(equality) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_211,plain,
% 7.71/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_202]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_203,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1648,plain,
% 7.71/1.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_203]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1649,plain,
% 7.71/1.49      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_1648]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22651,plain,
% 7.71/1.49      ( k2_tarski(X0,sK1) = sK0 | k1_tarski(X0) = sK0 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_22130,c_18,c_17,c_211,c_1649]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1,plain,
% 7.71/1.49      ( ~ r2_xboole_0(X0,X0) ),
% 7.71/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19716,plain,
% 7.71/1.49      ( r2_xboole_0(X0,X0) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_20691,plain,
% 7.71/1.49      ( r2_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_20290,c_19716]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22666,plain,
% 7.71/1.49      ( k1_tarski(X0) = sK0 | r2_xboole_0(sK0,k1_tarski(sK1)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_22651,c_20691]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22782,plain,
% 7.71/1.49      ( k1_tarski(X0) = sK0 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_22329,c_17,c_3845,c_19786,c_22666]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22811,plain,
% 7.71/1.49      ( sK0 != sK0 ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_22782,c_17]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22819,plain,
% 7.71/1.49      ( $false ),
% 7.71/1.49      inference(equality_resolution_simp,[status(thm)],[c_22811]) ).
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.49  
% 7.71/1.49  ------                               Statistics
% 7.71/1.49  
% 7.71/1.49  ------ Selected
% 7.71/1.49  
% 7.71/1.49  total_time:                             0.597
% 7.71/1.49  
%------------------------------------------------------------------------------
