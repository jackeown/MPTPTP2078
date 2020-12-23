%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:57 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 132 expanded)
%              Number of clauses        :   38 (  47 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 ( 296 expanded)
%              Number of equality atoms :   76 ( 131 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f39])).

fof(f63,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k6_subset_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_831,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_833,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1118,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_831,c_833])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_835,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1998,plain,
    ( k6_subset_1(k7_relat_1(sK4,X0),k7_relat_1(sK4,X1)) = k7_relat_1(sK4,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_831,c_835])).

cnf(c_2459,plain,
    ( k7_relat_1(sK4,k6_subset_1(k1_relat_1(sK4),X0)) = k6_subset_1(sK4,k7_relat_1(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_1118,c_1998])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_832,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_836,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k6_subset_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_837,plain,
    ( k6_subset_1(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1483,plain,
    ( k6_subset_1(X0,k6_subset_1(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_837])).

cnf(c_5839,plain,
    ( k6_subset_1(sK2,k6_subset_1(X0,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_832,c_1483])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_844,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5837,plain,
    ( k6_subset_1(X0,k6_subset_1(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_844,c_1483])).

cnf(c_12,plain,
    ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_839,plain,
    ( r1_xboole_0(k6_subset_1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_834,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1273,plain,
    ( k7_relat_1(k7_relat_1(X0,k6_subset_1(X1,X2)),X2) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_834])).

cnf(c_4390,plain,
    ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_831,c_1273])).

cnf(c_5914,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0),k6_subset_1(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5837,c_4390])).

cnf(c_6979,plain,
    ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,sK3)),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5839,c_5914])).

cnf(c_8285,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2459,c_6979])).

cnf(c_375,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1030,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_1031,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_60,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_51,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8285,c_1031,c_60,c_51,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.99  
% 4.02/0.99  ------  iProver source info
% 4.02/0.99  
% 4.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.99  git: non_committed_changes: false
% 4.02/0.99  git: last_make_outside_of_git: false
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  ------ Parsing...
% 4.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.99  ------ Proving...
% 4.02/0.99  ------ Problem Properties 
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  clauses                                 22
% 4.02/0.99  conjectures                             3
% 4.02/0.99  EPR                                     6
% 4.02/0.99  Horn                                    20
% 4.02/0.99  unary                                   7
% 4.02/0.99  binary                                  12
% 4.02/0.99  lits                                    40
% 4.02/0.99  lits eq                                 8
% 4.02/0.99  fd_pure                                 0
% 4.02/0.99  fd_pseudo                               0
% 4.02/0.99  fd_cond                                 0
% 4.02/0.99  fd_pseudo_cond                          1
% 4.02/0.99  AC symbols                              0
% 4.02/0.99  
% 4.02/0.99  ------ Input Options Time Limit: Unbounded
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  Current options:
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ Proving...
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS status Theorem for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  fof(f16,conjecture,(
% 4.02/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f17,negated_conjecture,(
% 4.02/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 4.02/0.99    inference(negated_conjecture,[],[f16])).
% 4.02/0.99  
% 4.02/0.99  fof(f28,plain,(
% 4.02/0.99    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 4.02/0.99    inference(ennf_transformation,[],[f17])).
% 4.02/0.99  
% 4.02/0.99  fof(f29,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 4.02/0.99    inference(flattening,[],[f28])).
% 4.02/0.99  
% 4.02/0.99  fof(f39,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f40,plain,(
% 4.02/0.99    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f39])).
% 4.02/0.99  
% 4.02/0.99  fof(f63,plain,(
% 4.02/0.99    v1_relat_1(sK4)),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f15,axiom,(
% 4.02/0.99    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f27,plain,(
% 4.02/0.99    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f15])).
% 4.02/0.99  
% 4.02/0.99  fof(f62,plain,(
% 4.02/0.99    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f27])).
% 4.02/0.99  
% 4.02/0.99  fof(f13,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f24,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2))),
% 4.02/0.99    inference(ennf_transformation,[],[f13])).
% 4.02/0.99  
% 4.02/0.99  fof(f60,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f24])).
% 4.02/0.99  
% 4.02/0.99  fof(f64,plain,(
% 4.02/0.99    r1_tarski(sK2,sK3)),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f9,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f23,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.02/0.99    inference(ennf_transformation,[],[f9])).
% 4.02/0.99  
% 4.02/0.99  fof(f56,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f23])).
% 4.02/0.99  
% 4.02/0.99  fof(f11,axiom,(
% 4.02/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f58,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f11])).
% 4.02/0.99  
% 4.02/0.99  fof(f74,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k6_subset_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f56,f58])).
% 4.02/0.99  
% 4.02/0.99  fof(f8,axiom,(
% 4.02/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f38,plain,(
% 4.02/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 4.02/0.99    inference(nnf_transformation,[],[f8])).
% 4.02/0.99  
% 4.02/0.99  fof(f54,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f38])).
% 4.02/0.99  
% 4.02/0.99  fof(f73,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k6_subset_1(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f54,f58])).
% 4.02/0.99  
% 4.02/0.99  fof(f3,axiom,(
% 4.02/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f36,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f3])).
% 4.02/0.99  
% 4.02/0.99  fof(f37,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(flattening,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f46,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.02/0.99    inference(cnf_transformation,[],[f37])).
% 4.02/0.99  
% 4.02/0.99  fof(f76,plain,(
% 4.02/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.02/0.99    inference(equality_resolution,[],[f46])).
% 4.02/0.99  
% 4.02/0.99  fof(f7,axiom,(
% 4.02/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f53,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f7])).
% 4.02/0.99  
% 4.02/0.99  fof(f71,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f53,f58])).
% 4.02/0.99  
% 4.02/0.99  fof(f14,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f25,plain,(
% 4.02/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 4.02/0.99    inference(ennf_transformation,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f26,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 4.02/0.99    inference(flattening,[],[f25])).
% 4.02/0.99  
% 4.02/0.99  fof(f61,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f26])).
% 4.02/0.99  
% 4.02/0.99  fof(f48,plain,(
% 4.02/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f37])).
% 4.02/0.99  
% 4.02/0.99  fof(f5,axiom,(
% 4.02/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f51,plain,(
% 4.02/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f5])).
% 4.02/0.99  
% 4.02/0.99  fof(f65,plain,(
% 4.02/0.99    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  cnf(c_22,negated_conjecture,
% 4.02/0.99      ( v1_relat_1(sK4) ),
% 4.02/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_831,plain,
% 4.02/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_19,plain,
% 4.02/0.99      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_833,plain,
% 4.02/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1118,plain,
% 4.02/0.99      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_831,c_833]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_17,plain,
% 4.02/0.99      ( ~ v1_relat_1(X0)
% 4.02/0.99      | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_835,plain,
% 4.02/0.99      ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1998,plain,
% 4.02/0.99      ( k6_subset_1(k7_relat_1(sK4,X0),k7_relat_1(sK4,X1)) = k7_relat_1(sK4,k6_subset_1(X0,X1)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_831,c_835]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2459,plain,
% 4.02/0.99      ( k7_relat_1(sK4,k6_subset_1(k1_relat_1(sK4),X0)) = k6_subset_1(sK4,k7_relat_1(sK4,X0)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1118,c_1998]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_21,negated_conjecture,
% 4.02/0.99      ( r1_tarski(sK2,sK3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_832,plain,
% 4.02/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_15,plain,
% 4.02/0.99      ( r1_xboole_0(X0,k6_subset_1(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 4.02/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_836,plain,
% 4.02/0.99      ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
% 4.02/0.99      | r1_tarski(X0,X2) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_14,plain,
% 4.02/0.99      ( ~ r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_837,plain,
% 4.02/0.99      ( k6_subset_1(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1483,plain,
% 4.02/0.99      ( k6_subset_1(X0,k6_subset_1(X1,X2)) = X0
% 4.02/0.99      | r1_tarski(X0,X2) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_836,c_837]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5839,plain,
% 4.02/0.99      ( k6_subset_1(sK2,k6_subset_1(X0,sK3)) = sK2 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_832,c_1483]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7,plain,
% 4.02/0.99      ( r1_tarski(X0,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_844,plain,
% 4.02/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5837,plain,
% 4.02/0.99      ( k6_subset_1(X0,k6_subset_1(X1,X0)) = X0 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_844,c_1483]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12,plain,
% 4.02/0.99      ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f71]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_839,plain,
% 4.02/0.99      ( r1_xboole_0(k6_subset_1(X0,X1),X1) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_18,plain,
% 4.02/0.99      ( ~ r1_xboole_0(X0,X1)
% 4.02/0.99      | ~ v1_relat_1(X2)
% 4.02/0.99      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_834,plain,
% 4.02/0.99      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 4.02/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1273,plain,
% 4.02/0.99      ( k7_relat_1(k7_relat_1(X0,k6_subset_1(X1,X2)),X2) = k1_xboole_0
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_839,c_834]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4390,plain,
% 4.02/0.99      ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,X1)),X1) = k1_xboole_0 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_831,c_1273]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5914,plain,
% 4.02/0.99      ( k7_relat_1(k7_relat_1(sK4,X0),k6_subset_1(X1,X0)) = k1_xboole_0 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5837,c_4390]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6979,plain,
% 4.02/0.99      ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,sK3)),sK2) = k1_xboole_0 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5839,c_5914]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8285,plain,
% 4.02/0.99      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) = k1_xboole_0 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2459,c_6979]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_375,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1030,plain,
% 4.02/0.99      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != X0
% 4.02/0.99      | k1_xboole_0 != X0
% 4.02/0.99      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_375]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1031,plain,
% 4.02/0.99      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
% 4.02/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_60,plain,
% 4.02/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 4.02/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10,plain,
% 4.02/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_51,plain,
% 4.02/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_20,negated_conjecture,
% 4.02/0.99      ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
% 4.02/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(contradiction,plain,
% 4.02/0.99      ( $false ),
% 4.02/0.99      inference(minisat,[status(thm)],[c_8285,c_1031,c_60,c_51,c_20]) ).
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  ------                               Statistics
% 4.02/0.99  
% 4.02/0.99  ------ Selected
% 4.02/0.99  
% 4.02/0.99  total_time:                             0.307
% 4.02/0.99  
%------------------------------------------------------------------------------
