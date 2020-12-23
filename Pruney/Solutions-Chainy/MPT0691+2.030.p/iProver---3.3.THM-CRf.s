%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:43 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 141 expanded)
%              Number of clauses        :   40 (  57 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   18
%              Number of atoms          :  120 ( 295 expanded)
%              Number of equality atoms :   55 (  81 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f34])).

fof(f53,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19739,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19746,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19952,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_19739,c_19746])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19738,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19743,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19988,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_19738,c_19743])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19744,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20014,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_19738,c_19744])).

cnf(c_14,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19742,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20249,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20014,c_19742])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19741,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19914,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_19738,c_19741])).

cnf(c_20257,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20249,c_19914])).

cnf(c_20258,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20257,c_19914])).

cnf(c_19,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19848,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_19849,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19848])).

cnf(c_20465,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20258,c_19,c_19849])).

cnf(c_20479,plain,
    ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19988,c_20465])).

cnf(c_20535,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19952,c_20479])).

cnf(c_20590,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) = sK0 ),
    inference(superposition,[status(thm)],[c_20535,c_19746])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19748,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19951,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_19748,c_19746])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20146,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_19951,c_0])).

cnf(c_20669,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_20590,c_20146])).

cnf(c_19876,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_19748])).

cnf(c_22437,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20669,c_19876])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22437,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.46/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/1.50  
% 7.46/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.46/1.50  
% 7.46/1.50  ------  iProver source info
% 7.46/1.50  
% 7.46/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.46/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.46/1.50  git: non_committed_changes: false
% 7.46/1.50  git: last_make_outside_of_git: false
% 7.46/1.50  
% 7.46/1.50  ------ 
% 7.46/1.50  ------ Parsing...
% 7.46/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  ------ Proving...
% 7.46/1.50  ------ Problem Properties 
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  clauses                                 18
% 7.46/1.50  conjectures                             3
% 7.46/1.50  EPR                                     3
% 7.46/1.50  Horn                                    18
% 7.46/1.50  unary                                   6
% 7.46/1.50  binary                                  9
% 7.46/1.50  lits                                    33
% 7.46/1.50  lits eq                                 7
% 7.46/1.50  fd_pure                                 0
% 7.46/1.50  fd_pseudo                               0
% 7.46/1.50  fd_cond                                 0
% 7.46/1.50  fd_pseudo_cond                          1
% 7.46/1.50  AC symbols                              0
% 7.46/1.50  
% 7.46/1.50  ------ Input Options Time Limit: Unbounded
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing...
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.46/1.50  Current options:
% 7.46/1.50  ------ 
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing...
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing...
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing...
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing...
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing...
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.46/1.50  
% 7.46/1.50  ------ Proving...
% 7.46/1.50  
% 7.46/1.50  
% 7.46/1.50  % SZS status Theorem for theBenchmark.p
% 7.46/1.50  
% 7.46/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.46/1.50  
% 7.46/1.50  fof(f15,conjecture,(
% 7.46/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f16,negated_conjecture,(
% 7.46/1.50    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.46/1.50    inference(negated_conjecture,[],[f15])).
% 7.46/1.50  
% 7.46/1.50  fof(f30,plain,(
% 7.46/1.50    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.46/1.50    inference(ennf_transformation,[],[f16])).
% 7.46/1.50  
% 7.46/1.50  fof(f31,plain,(
% 7.46/1.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 7.46/1.50    inference(flattening,[],[f30])).
% 7.46/1.50  
% 7.46/1.50  fof(f34,plain,(
% 7.46/1.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 7.46/1.50    introduced(choice_axiom,[])).
% 7.46/1.50  
% 7.46/1.50  fof(f35,plain,(
% 7.46/1.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 7.46/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f34])).
% 7.46/1.50  
% 7.46/1.50  fof(f53,plain,(
% 7.46/1.50    r1_tarski(sK0,k1_relat_1(sK1))),
% 7.46/1.50    inference(cnf_transformation,[],[f35])).
% 7.46/1.50  
% 7.46/1.50  fof(f8,axiom,(
% 7.46/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f22,plain,(
% 7.46/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.46/1.50    inference(ennf_transformation,[],[f8])).
% 7.46/1.50  
% 7.46/1.50  fof(f45,plain,(
% 7.46/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f22])).
% 7.46/1.50  
% 7.46/1.50  fof(f52,plain,(
% 7.46/1.50    v1_relat_1(sK1)),
% 7.46/1.50    inference(cnf_transformation,[],[f35])).
% 7.46/1.50  
% 7.46/1.50  fof(f12,axiom,(
% 7.46/1.50    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f27,plain,(
% 7.46/1.50    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 7.46/1.50    inference(ennf_transformation,[],[f12])).
% 7.46/1.50  
% 7.46/1.50  fof(f49,plain,(
% 7.46/1.50    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f27])).
% 7.46/1.50  
% 7.46/1.50  fof(f11,axiom,(
% 7.46/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f26,plain,(
% 7.46/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.46/1.50    inference(ennf_transformation,[],[f11])).
% 7.46/1.50  
% 7.46/1.50  fof(f48,plain,(
% 7.46/1.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f26])).
% 7.46/1.50  
% 7.46/1.50  fof(f13,axiom,(
% 7.46/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f28,plain,(
% 7.46/1.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.46/1.50    inference(ennf_transformation,[],[f13])).
% 7.46/1.50  
% 7.46/1.50  fof(f50,plain,(
% 7.46/1.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f28])).
% 7.46/1.50  
% 7.46/1.50  fof(f14,axiom,(
% 7.46/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f29,plain,(
% 7.46/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.46/1.50    inference(ennf_transformation,[],[f14])).
% 7.46/1.50  
% 7.46/1.50  fof(f51,plain,(
% 7.46/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f29])).
% 7.46/1.50  
% 7.46/1.50  fof(f10,axiom,(
% 7.46/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f25,plain,(
% 7.46/1.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.46/1.50    inference(ennf_transformation,[],[f10])).
% 7.46/1.50  
% 7.46/1.50  fof(f47,plain,(
% 7.46/1.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f25])).
% 7.46/1.50  
% 7.46/1.50  fof(f6,axiom,(
% 7.46/1.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f43,plain,(
% 7.46/1.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f6])).
% 7.46/1.50  
% 7.46/1.50  fof(f1,axiom,(
% 7.46/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.46/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.46/1.50  
% 7.46/1.50  fof(f36,plain,(
% 7.46/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.46/1.50    inference(cnf_transformation,[],[f1])).
% 7.46/1.50  
% 7.46/1.50  fof(f54,plain,(
% 7.46/1.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 7.46/1.50    inference(cnf_transformation,[],[f35])).
% 7.46/1.50  
% 7.46/1.50  cnf(c_17,negated_conjecture,
% 7.46/1.50      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 7.46/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19739,plain,
% 7.46/1.50      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 7.46/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_9,plain,
% 7.46/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.46/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19746,plain,
% 7.46/1.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.46/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19952,plain,
% 7.46/1.50      ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
% 7.46/1.50      inference(superposition,[status(thm)],[c_19739,c_19746]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_18,negated_conjecture,
% 7.46/1.50      ( v1_relat_1(sK1) ),
% 7.46/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19738,plain,
% 7.46/1.50      ( v1_relat_1(sK1) = iProver_top ),
% 7.46/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_13,plain,
% 7.46/1.50      ( ~ v1_relat_1(X0)
% 7.46/1.50      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 7.46/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19743,plain,
% 7.46/1.50      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 7.46/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.46/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19988,plain,
% 7.46/1.50      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 7.46/1.50      inference(superposition,[status(thm)],[c_19738,c_19743]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_12,plain,
% 7.46/1.50      ( ~ v1_relat_1(X0)
% 7.46/1.50      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.46/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19744,plain,
% 7.46/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.46/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.46/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_20014,plain,
% 7.46/1.50      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 7.46/1.50      inference(superposition,[status(thm)],[c_19738,c_19744]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_14,plain,
% 7.46/1.50      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
% 7.46/1.50      | ~ v1_relat_1(X0) ),
% 7.46/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_19742,plain,
% 7.46/1.50      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
% 7.46/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.46/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.46/1.50  
% 7.46/1.50  cnf(c_20249,plain,
% 7.46/1.50      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) = iProver_top
% 7.46/1.50      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_20014,c_19742]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_15,plain,
% 7.46/1.51      ( ~ v1_relat_1(X0)
% 7.46/1.51      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 7.46/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19741,plain,
% 7.46/1.51      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 7.46/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.46/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19914,plain,
% 7.46/1.51      ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_19738,c_19741]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20257,plain,
% 7.46/1.51      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) = iProver_top
% 7.46/1.51      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 7.46/1.51      inference(light_normalisation,[status(thm)],[c_20249,c_19914]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20258,plain,
% 7.46/1.51      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = iProver_top
% 7.46/1.51      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 7.46/1.51      inference(demodulation,[status(thm)],[c_20257,c_19914]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19,plain,
% 7.46/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 7.46/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_11,plain,
% 7.46/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.46/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19848,plain,
% 7.46/1.51      ( v1_relat_1(k7_relat_1(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 7.46/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19849,plain,
% 7.46/1.51      ( v1_relat_1(k7_relat_1(sK1,X0)) = iProver_top
% 7.46/1.51      | v1_relat_1(sK1) != iProver_top ),
% 7.46/1.51      inference(predicate_to_equality,[status(thm)],[c_19848]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20465,plain,
% 7.46/1.51      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = iProver_top ),
% 7.46/1.51      inference(global_propositional_subsumption,
% 7.46/1.51                [status(thm)],
% 7.46/1.51                [c_20258,c_19,c_19849]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20479,plain,
% 7.46/1.51      ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = iProver_top ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_19988,c_20465]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20535,plain,
% 7.46/1.51      ( r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) = iProver_top ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_19952,c_20479]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20590,plain,
% 7.46/1.51      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) = sK0 ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_20535,c_19746]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_7,plain,
% 7.46/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.46/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19748,plain,
% 7.46/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 7.46/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19951,plain,
% 7.46/1.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_19748,c_19746]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_0,plain,
% 7.46/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.46/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20146,plain,
% 7.46/1.51      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_19951,c_0]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_20669,plain,
% 7.46/1.51      ( k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = sK0 ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_20590,c_20146]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_19876,plain,
% 7.46/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_0,c_19748]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_22437,plain,
% 7.46/1.51      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 7.46/1.51      inference(superposition,[status(thm)],[c_20669,c_19876]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_16,negated_conjecture,
% 7.46/1.51      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 7.46/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(c_21,plain,
% 7.46/1.51      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 7.46/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.46/1.51  
% 7.46/1.51  cnf(contradiction,plain,
% 7.46/1.51      ( $false ),
% 7.46/1.51      inference(minisat,[status(thm)],[c_22437,c_21]) ).
% 7.46/1.51  
% 7.46/1.51  
% 7.46/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.46/1.51  
% 7.46/1.51  ------                               Statistics
% 7.46/1.51  
% 7.46/1.51  ------ Selected
% 7.46/1.51  
% 7.46/1.51  total_time:                             0.57
% 7.46/1.51  
%------------------------------------------------------------------------------
